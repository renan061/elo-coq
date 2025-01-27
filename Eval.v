From Coq Require Import PeanoNat.
From Coq Require Import Program.Basics.
From Coq Require Import Strings.String.

From Elo Require Import Core.

Inductive Result : Set :=
  | Ok      : mem -> tm -> Result
  | Spawn   : mem -> tm -> tm -> Result
  | Value   : Result
  | Waiting : addr -> Result
  | Error   : string -> Result
  .

Definition bind (r : Result) (f : tm -> tm) : Result :=
  match r with
  | Ok m t       => Ok m (f t)
  | Spawn m t t' => Spawn m (f t) t'
  | Value        => Value
  | Waiting ad   => Waiting ad
  | Error s      => Error s
  end.

Local Notation "r '>>=' f" := (bind r f) (no associativity, at level 10).

(* ------------------------------------------------------------------------- *)
(* eval                                                                      *)
(* ------------------------------------------------------------------------- *)

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

Definition _new m t T R :=
  let ad := #m in Ok (m +++ new_cell T R) <{init ad t : T}>.

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
      | Some tx => Ok m[ad.X <- true] <{cr ad ([SELF := &ad : T][x := tx]t)}>
      | None    => Error "attempt to read empty memory cell"
      end
  | _ => Error "expecting <{acq (&_ : _) _ _}>"
  end.

Definition _cr m t : Result :=
  match t with
  | <{cr ad t}> => Ok m[ad.X <- false] t
  | _ => Error "expecting <{cr _ _}>"
  end.

Definition _wait m t : Result :=
  match t with
  | <{wait (&ad : T)}> => Ok m[ad.X <- false] <{reacq ad}>
  | _                  => Error "expecting <{wait (&_ : _)}>"
  end.

Definition _reacq m ad : Result :=
  if m[ad].X
    then Waiting ad
    else Ok m[ad.X <- true] <{unit}>.

(* ------------------------------------------------------------------------- *)

Fixpoint eval (m : mem) (t : tm) : Result :=
  let do1 := fun m t (C : tm -> tm) (R : Result) =>
    if is_value t then R else eval m t >>= C
  in
  let do2 := fun m t1 t2 (C : tm -> tm -> tm) (R : Result) =>
    do1 m t1 (flip C t2) (do1 m t2 (C t1) R)
  in
  match t with
  | <{unit                     }> => Value
  | <{nat _                    }> => Value
  | <{t1 + t2                  }> => do2 m t1 t2 tm_plus (_plus m t)
  | <{t1 - t2                  }> => do2 m t1 t2 tm_monus (_monus m t)
  | <{t1; t2                   }> => do1 m t1 (flip tm_seq t2) (Ok m t2)
  | <{if t1 then t2 else t3 end}> => do1 m t1 (C_if t2 t3) (_if m t)
  | <{while t1 do t2 end       }> => _while m t1 t2
  | <{var _                    }> => Error "cannot evaluate variables"
  | <{fn _ _ _                 }> => Value
  | <{call t1 t2               }> => do2 m t1 t2 tm_call (_call m t)
  | <{&_ : _                   }> => Value
  | <{new t : T                }> => _new m t T R_invalid
  | <{init ad t' : T           }> => do1 m t' (C_init ad T) (_init m t)
  | <{*t'                      }> => do1 m t' tm_load (_load m t)
  | <{t1 := t2                 }> => do2 m t1 t2 tm_asg (_asg m t)
  | <{acq t1 x t2              }> => do1 m t1 (C_acq x t2) (_acq m t)
  | <{cr ad t'                 }> => do1 m t' (tm_cr ad) (_cr m t)
  | <{wait _                   }> => _wait m t
  | <{reacq ad                 }> => _reacq m ad
  | <{spawn t'                 }> => Spawn m <{unit}> t'
  end.

(* ------------------------------------------------------------------------- *)
(* elo                                                                       *)
(* ------------------------------------------------------------------------- *)

Inductive Results : Set :=
  | cont : mem -> threads -> Results -> Results
  | done : mem -> threads -> string -> Results
  .

Fixpoint elo (m : mem) (ths : threads) gas tid : Results :=
  match gas with
  | 0      => done m ths "out of gas"
  | S gas' =>
    match eval m ths[tid] with
    | Ok m' t' =>
        let ths' := ths[tid <- t'] in
        let tid' := if Compare_dec.lt_dec (S tid) (#ths) then S tid else 0 in
        cont m' ths' (elo m' ths' gas' tid')
    | Spawn m' t' t'' =>
        let ths' := ths[tid <- t'] +++ t'' in
        let tid' := if Compare_dec.lt_dec (S tid) (#ths) then S tid else 0 in
        cont m' ths' (elo m' ths' gas' tid')
    | Value =>
        let tid' := if Compare_dec.lt_dec (S tid) (#ths) then S tid else 0 in
        cont m ths (elo m ths gas' tid')
    | Waiting ad =>
        let tid' := if Compare_dec.lt_dec (S tid) (#ths) then S tid else 0 in
        cont m ths (elo m ths gas' tid')
    | Error s =>
        done m ths s
    end
  end.

Fixpoint last_result (ress : Results) : Results :=
  match ress with
  | done m ths s => ress
  | cont _ _ ress'  => last_result ress'
  end.

(* mstep-to-eval ----------------------------------------------------------- *)

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

Local Lemma mstep_to_eval : forall m1 m2 t1 t2 e,
  m1 \ t1 ==[e]==> m2 \ t2 ->
  eval m1 t1 = Ok m2 t2.
Proof.
  intros. invc_mstep; ind_tstep;
  unfold eval; fold eval; repeat iota; trivial;
  repeat spec; try rewrite IHtstep; unfold flip; simpl; eauto.
  - destruct (m2[ad].t); auto. invc_eq. reflexivity.
  - destruct (m1[ad].X); auto. destruct (m1[ad].t); auto. invc_eq. reflexivity.
  - unfold _reacq. destruct (m1[ad].X); auto.
Qed.

(* eval-to-mstep & eval-to-cstep ------------------------------------------- *)

Local Lemma value_from_isvalue : forall t,
  is_value t = true ->
  value t.
Proof.
  intros * H. destruct t; eauto using value; cbv in H; auto.
Qed.

Local Ltac solve_eval_to_step :=
  match goal with
  (* simpl eval ------------------------------------------------------------ *)
  | Heq : eval ?m _ = _ |- _ =>
      simpl eval in Heq; repeat solve_eval_to_step
  (* destroying is_value inside conditionals ------------------------------- *)
  | Heq : context[if is_value ?t then _ else _] |- _ =>
      destruct (is_value t) eqn:?Heq
  (* converting is_value to value ------------------------------------------ *)
  | H : is_value ?t = true |- _ =>
      assert (value t) by eauto using value_from_isvalue; clear H
  (* destroying the eval inside the monadic bind --------------------------- *)
  | Heq : (eval ?m ?t) >>= _ = _ |- _ =>
      destruct (eval m t); invc Heq
  (* destroying match of terms --------------------------------------------- *)
  | Heq : (match ?t with _ => _ end) = _ |- _ => 
      destruct t eqn:?Ht ; invc Heq
  (* specializing the induction hypothesis --------------------------------- *)
  | IH : forall _ _, ?C ?m ?t = ?C _ _ -> _ |- _ =>
      specialize (IH m t eq_refl) as [e ?]; auto
  | IH : forall _ _ _, ?C ?m ?t ?t' = ?C _ _ _ -> _
  |- _ --[e_spawn ?tid _]--> _ =>
      specialize (IH tid t' t eq_refl)
  (* solving the inductive case -------------------------------------------- *)
  | _ : _ \ _ ==[?e]==> _ \ _ |- exists _, _ =>
      exists e; invc_mstep; eauto using tstep, mstep
  (* ----------------------------------------------------------------------- *)
  | Heq : Ok _ _      = Ok _ _      |- _ => invc Heq
  | Heq : Spawn _ _ _ = Spawn _ _ _ |- _ => invc Heq
  | Heq : Ok _ _      = Spawn _ _ _ |- _ => invc Heq
  (* solving for while ----------------------------------------------------- *)
  | Heq : _while _ _ _ = _ |- _ =>
      invc Heq; eauto using tstep, mstep
  (* solving for alloc ----------------------------------------------------- *)
  | Heq : _new _ _ _ _ = _ |- _ =>
      invc Heq; eauto using tstep, mstep
  (* solving for read ------------------------------------------------------ *)
  | _ : ?m[?ad].t = _ |- exists _, _ \ <{*(&_ : _)}> ==[_]==> _ \ _ =>
      assert (ad < #m) by (lt_eq_gt ad (#m); trivial; sigma; upsilon; auto);
      eauto using tstep, mstep
  (* solving for acq ------------------------------------------------------- *)
  | H : ?m[?ad].t = _ |- exists _, _ \ <{acq (&_ : _) _ _}> ==[_]==> _ \ _ =>
      assert (ad < #m) by (lt_eq_gt ad (#m); trivial; sigma; upsilon; auto);
      rewrite <- H; eauto using tstep, mstep
  (* solving for reacq ----------------------------------------------------- *)
  | H : _reacq ?m ?ad = _ |- _ =>
      unfold _reacq in H; destruct (m[ad].X) eqn:?; invc H
  end.

Local Lemma eval_to_mstep : forall m1 m2 t1 t2,
  eval m1 t1 = Ok m2 t2 ->
  exists e, m1 \ t1 ==[e]==> m2 \ t2.
Proof.
  intros * Heq. gendep t2. gendep m2.
  induction t1; intros; try solve [invc Heq];
  solve_eval_to_step; eauto using tstep, mstep.
Qed.

Local Lemma eval_to_cstep : forall m t1 t2 t,
  eval m t1 = Spawn m t2 t ->
  t1 --[e_spawn t]--> t2.
Proof.
  intros * Heq. gendep t2. gendep t.
  induction t1; intros; try solve [invc Heq];
  solve_eval_to_step; eauto using tstep.
Qed.

