From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-waits                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive no_waits : tm -> Prop :=
  | nowaits_unit  :                  no_waits <{unit                     }>
  | nowaits_nat   : forall n,        no_waits <{nat n                    }>
  | nowaits_plus  : forall t1 t2,    no_waits t1 ->
                                     no_waits t2 ->
                                     no_waits <{t1 + t2                  }>
  | nowaits_monus : forall t1 t2,    no_waits t1 ->
                                     no_waits t2 ->
                                     no_waits <{t1 - t2                  }>
  | nowaits_seq   : forall t1 t2,    no_waits t1 ->
                                     no_waits t2 ->
                                     no_waits <{t1; t2                   }>
  | nowaits_if    : forall t1 t2 t3, no_waits t1 ->
                                     no_waits t2 ->
                                     no_waits t3 ->
                                     no_waits <{if t1 then t2 else t3 end}>
  | nowaits_while : forall t1 t2,    no_waits t1 ->
                                     no_waits t2 ->
                                     no_waits <{while t1 do t2 end       }>
  | nowaits_var   : forall x,        no_waits <{var x                    }>
  | nowaits_fun   : forall x Tx t,   no_waits t  ->
                                     no_waits <{fn x Tx t                }>
  | nowaits_call  : forall t1 t2,    no_waits t1 ->
                                     no_waits t2 ->
                                     no_waits <{call t1 t2               }>
  | nowaits_ref   : forall ad T,     no_waits <{&ad : T                  }>
  | nowaits_new   : forall t T,      no_waits t  ->
                                     no_waits <{new t : T                }>
  | nowaits_init  : forall ad t T,   no_waits t  ->
                                     no_waits <{init ad t : T            }>
  | nowaits_load  : forall t,        no_waits t  ->
                                     no_waits <{*t                       }>
  | nowaits_asg   : forall t1 t2,    no_waits t1 ->
                                     no_waits t2 ->
                                     no_waits <{t1 := t2                 }>
  | nowaits_acq   : forall t1 x t2,  no_waits t1 ->
                                     no_waits t2 ->
                                     no_waits <{acq t1 x t2              }>
  | nowaits_cr    : forall ad t,     no_waits t  ->
                                     no_waits <{cr ad t                  }>
  | nowaits_reacq : forall ad,       no_waits <{reacq ad                 }>
  | nowaits_spawn : forall t,        no_waits t  ->
                                     no_waits <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _nowaits tt :=
  match goal with
  | H : no_waits <{unit                  }> |- _ => clear H
  | H : no_waits <{nat _                 }> |- _ => clear H
  | H : no_waits <{_ + _                 }> |- _ => tt H
  | H : no_waits <{_ - _                 }> |- _ => tt H
  | H : no_waits <{_; _                  }> |- _ => tt H
  | H : no_waits <{if _ then _ else _ end}> |- _ => tt H
  | H : no_waits <{while _ do _ end      }> |- _ => tt H
  | H : no_waits <{var _                 }> |- _ => clear H
  | H : no_waits <{fn _ _ _              }> |- _ => tt H
  | H : no_waits <{call _ _              }> |- _ => tt H
  | H : no_waits <{&_ : _                }> |- _ => clear H
  | H : no_waits <{new _ : _             }> |- _ => tt H
  | H : no_waits <{init _ _ : _          }> |- _ => tt H
  | H : no_waits <{* _                   }> |- _ => tt H
  | H : no_waits <{_ := _                }> |- _ => tt H
  | H : no_waits <{acq _ _ _             }> |- _ => tt H
  | H : no_waits <{cr _ _                }> |- _ => tt H
  | H : no_waits <{wait _                }> |- _ => invc H
  | H : no_waits <{reacq _               }> |- _ => clear H
  | H : no_waits <{spawn _               }> |- _ => tt H
  end.

Ltac inv_nowaits  := _nowaits inv.
Ltac invc_nowaits := _nowaits invc.

(* decidability ------------------------------------------------------------ *)

Lemma nowaits_dec : forall t,
  Decidable.decidable (no_waits t).
Proof.
  unfold Decidable.decidable. unfold not. intros.
  induction t; auto using no_waits;
  (destruct IHt1, IHt2, IHt3 || destruct IHt1, IHt2 || destruct IHt);
  auto using no_waits; right; intros; invc_nowaits; auto.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma nowaits_wrel_contradiction : forall t1 t2 ad,
  no_waits t1 ->
  t1 --[e_wrel ad]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_nowaits; auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma nowaits_subst : forall x tx t,
  no_waits t  ->
  no_waits tx ->
  no_waits <{[x := tx] t}>.
Proof.
  intros. induction t; invc_nowaits;
  simpl; repeat destruct _str_eq_dec; auto using no_waits.
Qed.

