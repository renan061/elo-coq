From Coq Require Import Program.Basics.
From Coq Require Import Strings.String.

From Elo Require Import Core.

Inductive Result : Set :=
  | Ok      : mem -> tm -> Result
  | Spawn   : mem -> tm -> tm -> Result
  | Waiting : addr -> Result
  | Error   : string -> Result
  .

Definition bind (r : Result) (f : tm -> tm) : Result :=
  match r with
  | Ok m t       => Ok m (f t)
  | Spawn m t t' => Spawn m (f t) t'
  | Waiting ad   => Waiting ad
  | Error s      => Error s
  end.

Local Notation "r '>>=' f" := (bind r f) (no associativity, at level 10).

Definition _plus m t : Result :=
  match t with
  | <{nat n1 + nat n2}> => Ok m <{nat (n1 + n2)}>
  | _ => Error "expecting <{_ + _}>"
  end.

Definition _monus m t : Result :=
  match t with
  | <{nat n1 - nat n2}> => Ok m <{nat (n1 - n2)}>
  | _ => Error "expecting <{_ - _}>"
  end.

Definition C_if t2 t3 := fun t1' => <{if t1' then t2 else t3 end}>.

Definition _if m t : Result :=
  match t with
  | <{if nat O     then t2 else t3 end}> => Ok m t3
  | <{if nat (S _) then t2 else t3 end}> => Ok m t2
  | _ => Error "expecting <{if _ then _ else _ end}>"
  end.

Definition _while (m : mem) t1 t2 :=
  Ok m <{if t1 then t2; while t1 do t2 end else unit end}>.

Definition _call m t : Result :=
  match t with
  | <{call (fn x _ t) tx}> => Ok m <{[x := tx] t}>
  | _ => Error "expecting <{call (fn _ _ _) _}>"
  end.

Definition _new m t T :=
  let ad := #m in Ok (m +++ new_cell T) <{init ad t : T}>.

Definition C_init ad T := fun t' => <{init ad t' : T}>.

Definition _init m t : Result :=
  match t with
  | <{init ad t : T}> => Ok m[ad.t <- t] <{&ad : T}>
  | _ => Error "expecting <{init _ _ : _}>"
  end.

Definition _load m t : Result :=
  match t with
  | <{* (&ad : T)}> =>
    match m[ad].t with
    | Some t => Ok m t
    | None   => Error "attempt to read empty memory cell"
    end  
  | _ => Error "expecting <{* (&_ : _)}>"
  end.

Definition _asg m t : Result :=
  match t with
  | <{(&ad : T) := t}> => Ok m[ad.t <- t] <{unit}>
  | _ => Error "expecting <{(&_ : _) := _}>"
  end.

Definition C_acq x t2 := fun t1' => <{acq t1' x t2}>.

Definition _acq m t : Result :=
  match t with
  | <{acq (&ad : T) x t}> =>
    if m[ad].X then
      Waiting ad
    else
      match m[ad].t with
      | Some tx => Ok m[ad.X <- true] <{cr ad ([x := tx]t)}>
      | None    => Error "attempt to read empty memory cell"
      end
  | _ => Error "expecting <{acq (&_ : _) _ _}>"
  end.

Definition _cr m t : Result :=
  match t with
  | <{cr ad t}> => Ok m[ad.X <- false] t
  | _ => Error "expecting <{cr _ _}>"
  end.

Fixpoint eval (m : mem) (t : tm) : Result :=
  let do1 := fun m t (C : tm -> tm) (R : Result) =>
    if is_value t then R else eval m t >>= C
  in
  let do2 := fun m t1 t2 (C : tm -> tm -> tm) (R : Result) =>
    do1 m t1 (flip C t2) (do1 m t2 (C t1) R)
  in
  match t with
  | <{unit                     }> => Ok m t
  | <{nat _                    }> => Ok m t
  | <{t1 + t2                  }> => do2 m t1 t2 tm_plus (_plus m t)
  | <{t1 - t2                  }> => do2 m t1 t2 tm_monus (_monus m t)
  | <{t1; t2                   }> => do1 m t1 (flip tm_seq t2) (Ok m t2)
  | <{if t1 then t2 else t3 end}> => do1 m t1 (C_if t2 t3) (_if m t)
  | <{while t1 do t2 end       }> => _while m t1 t2
  | <{var _                    }> => Ok m t
  | <{fn _ _ _                 }> => Ok m t
  | <{call t1 t2               }> => do2 m t1 t2 tm_call (_call m t)
  | <{&_ : _                   }> => Ok m t
  | <{new t : T                }> => _new m t T
  | <{init ad t' : T           }> => do1 m t' (C_init ad T) (_init m t)
  | <{*t'                      }> => do1 m t' tm_load (_load m t)
  | <{t1 := t2                 }> => do2 m t1 t2 tm_asg (_asg m t)
  | <{acq t1 x t2              }> => do1 m t1 (C_acq x t2) (_acq m t)
  | <{cr ad t'                 }> => do1 m t' (tm_cr ad) (_cr m t)
  | <{spawn t'                 }> => Spawn m <{unit}> t'
  end.

(* -------------------------------------------------------------------------- *)

Local Lemma isvalue_from_tstep : forall t1 t2 e,
  t1 --[e]--> t2 ->
  is_value t1 = false.
Proof.
  intros. destruct t1; invc_tstep; cbv; reflexivity.
Qed.

Local Lemma isvalue_from_value : forall t,
  value t ->
  is_value t = true.
Proof.
  intros * Hval. destruct t; invc Hval; cbv; reflexivity.
Qed.

Local Lemma isvalue_from_notvalue : forall t,
  ~ value t ->
  is_value t = false.
Proof.
  intros * Hval. destruct t; auto; exfalso; eauto using value.
Qed.

Local Ltac iota :=
  match goal with
  | Htstep : ?t --[?e]--> ?t'
  |- context[if is_value ?t then _ else _] =>
    rewrite (isvalue_from_tstep t t' e Htstep)
  (* --- *)
  | Htstep : ?t --[?e]--> ?t'
  , Hif : context[if is_value ?t then _ else _]
  |- _ =>
    rewrite (isvalue_from_tstep t t' e Htstep) in Hif
  (* --- *)
  | Hval : value ?t
  |- context[if is_value ?t then _ else _] =>
    rewrite (isvalue_from_value t Hval)
  (* --- *)
  | Hval : value ?t
  , Hif : context[if is_value ?t then _ else _]
  |- _ =>
    rewrite (isvalue_from_value t Hval) in Hif
  (* --- *)
  | Hnval : ~ value ?t
  |- context[if is_value ?t then _ else _] =>
    rewrite (isvalue_from_notvalue t Hnval)
  (* --- *)
  | Hnval : ~ value ?t
  , Hif : context[if is_value ?t then _ else _]
  |- _ =>
    rewrite (isvalue_from_notvalue t Hnval) in Hif
  (* --- *)
  | |- context[if is_value <{&?ad : ?T}> then _ else _] =>
    rewrite (isvalue_from_value <{&ad : T}>); eauto using value
  | Hif : context[if is_value <{&?ad : ?T}> then _ else _] |- _ =>
    rewrite (isvalue_from_value <{&ad : T}>) in Hif; eauto using value
  end.

(* -------------------------------------------------------------------------- *)

Local Lemma mstep_to_eval : forall m1 m2 t1 t2 e,
  m1 \ t1 ==[e]==> m2 \ t2 ->
  eval m1 t1 = Ok m2 t2.
Proof.
  intros. invc_mstep;
  ind_tstep; repeat spec;
  unfold eval; fold eval; repeat iota; trivial;
  try rewrite IHtstep; unfold flip; simpl; trivial.
  - destruct (m2[ad].t); auto. invc_eq. reflexivity.
  - destruct (m1[ad].X); auto. destruct (m1[ad].t); auto. invc_eq. trivial.
Qed.

(* -------------------------------------------------------------------------- *)

Local Lemma eval_value : forall m t,
  value t ->
  eval m t = Ok m t.
Proof.
  intros * Hval. invc Hval; trivial.
Qed.

Local Lemma eval_to_mstep : forall m1 m2 t1 t2,
  eval m1 t1 = Ok m2 t2 ->
  value t1 \/ exists e, m1 \ t1 ==[e]==> m2 \ t2.
Proof.
  intros * Heq. gendep t2. gendep m2.
  induction t1; intros;
  try solve [left; auto using value];
  right.
  - unfold eval in Heq. fold eval in Heq.
    destruct (value_dec t1_1), (value_dec t1_2); repeat iota.
    + destruct t1_1; try solve [invc Heq].
      destruct t1_2; invc Heq.
      eauto using tstep, mstep.
    + specialize (IHt1_1 m1 t1_1).
      rewrite eval_value in IHt1_1; trivial.
      specialize (IHt1_1 eq_refl) as [? | [? ?]].
      * clean.
        unfold bind in Heq.
        destruct (eval m1 t1_2); invc Heq.
        specialize (IHt1_2 m2 t eq_refl) as [? | [? ?]]; auto.
        exists x. invc_mstep; eauto using tstep, mstep.
      * invc_mstep; value_does_not_step.
    + specialize (IHt1_2 m1 t1_2).
      rewrite eval_value in IHt1_2; trivial.
      specialize (IHt1_2 eq_refl) as [? | [? ?]].
      * clean.
        unfold bind in Heq.
        destruct (eval m1 t1_1); invc Heq.
        specialize (IHt1_1 m2 t eq_refl) as [? | [? ?]]; auto.
        exists x. invc_mstep; eauto using tstep, mstep.
      * invc_mstep; value_does_not_step.
    + unfold bind in Heq.
      destruct (eval m1 t1_1); invc Heq.
      specialize (IHt1_1 m2 t eq_refl) as [? | [? ?]]; auto.
      exists x. invc_mstep; eauto using tstep, mstep.
  - admit.
Qed.

