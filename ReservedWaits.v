From Elo Require Import Core.

From Elo Require Import NoWaits.

(* ------------------------------------------------------------------------- *)
(* reserved-waits                                                            *)
(* ------------------------------------------------------------------------- *)

Inductive reserved_waits : tm -> Prop :=
  | rwaits_unit  :                  reserved_waits <{unit                     }>
  | rwaits_nat   : forall n,        reserved_waits <{nat n                    }>
  | rwaits_plus  : forall t1 t2,    reserved_waits t1 ->
                                    reserved_waits t2 ->
                                    reserved_waits <{t1 + t2                  }>
  | rwaits_monus : forall t1 t2,    reserved_waits t1 ->
                                    reserved_waits t2 ->
                                    reserved_waits <{t1 - t2                  }>
  | rwaits_seq   : forall t1 t2,    reserved_waits t1 ->
                                    reserved_waits t2 ->
                                    reserved_waits <{t1; t2                   }>
  | rwaits_if    : forall t1 t2 t3, reserved_waits t1 ->
                                    reserved_waits t2 ->
                                    reserved_waits t3 ->
                                    reserved_waits <{if t1 then t2 else t3 end}>
  | rwaits_while : forall t1 t2,    reserved_waits t1 ->
                                    reserved_waits t2 ->
                                    reserved_waits <{while t1 do t2 end       }>
  | rwaits_var   : forall x,        reserved_waits <{var x                    }>
  | rwaits_fun   : forall x Tx t,   reserved_waits t  ->
                                    reserved_waits <{fn x Tx t                }>
  | rwaits_call  : forall t1 t2,    reserved_waits t1 ->
                                    reserved_waits t2 ->
                                    reserved_waits <{call t1 t2               }>
  | rwaits_ref   : forall ad T,     reserved_waits <{&ad : T                  }>
  | rwaits_new   : forall t T,      reserved_waits t  ->
                                    reserved_waits <{new t : T                }>
  | rwaits_init  : forall ad t T,   reserved_waits t  ->
                                    reserved_waits <{init ad t : T            }>
  | rwaits_load  : forall t,        reserved_waits t  ->
                                    reserved_waits <{*t                       }>
  | rwaits_asg   : forall t1 t2,    reserved_waits t1 ->
                                    reserved_waits t2 ->
                                    reserved_waits <{t1 := t2                 }>
  | rwaits_acq   : forall t1 x t2,  reserved_waits t1 ->
                                    reserved_waits t2 ->
                                    reserved_waits <{acq t1 x t2              }>
  | rwaits_cr    : forall ad t,     reserved_waits t  ->
                                    reserved_waits <{cr ad t                  }>
  | rwaits_wait  :                  reserved_waits <{wait (var SELF)          }>
  | rwaits_reacq : forall ad,       reserved_waits <{reacq ad                 }>
  | rwaits_spawn : forall t,        reserved_waits t ->
                                    reserved_waits <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _rwaits tt :=
  match goal with
  | H : reserved_waits <{unit                  }> |- _ => clear H
  | H : reserved_waits <{nat _                 }> |- _ => clear H
  | H : reserved_waits <{_ + _                 }> |- _ => tt H
  | H : reserved_waits <{_ - _                 }> |- _ => tt H
  | H : reserved_waits <{_; _                  }> |- _ => tt H
  | H : reserved_waits <{if _ then _ else _ end}> |- _ => tt H
  | H : reserved_waits <{while _ do _ end      }> |- _ => tt H
  | H : reserved_waits <{var _                 }> |- _ => clear H
  | H : reserved_waits <{fn _ _ _              }> |- _ => tt H
  | H : reserved_waits <{call _ _              }> |- _ => tt H
  | H : reserved_waits <{&_ : _                }> |- _ => clear H
  | H : reserved_waits <{new _ : _             }> |- _ => tt H
  | H : reserved_waits <{init _ _ : _          }> |- _ => tt H
  | H : reserved_waits <{* _                   }> |- _ => tt H
  | H : reserved_waits <{_ := _                }> |- _ => tt H
  | H : reserved_waits <{acq _ _ _             }> |- _ => tt H
  | H : reserved_waits <{cr _ _                }> |- _ => tt H
  | H : reserved_waits <{wait _                }> |- _ => tt H
  | H : reserved_waits <{reacq _               }> |- _ => clear H
  | H : reserved_waits <{spawn _               }> |- _ => tt H
  end.

Ltac inv_rwaits  := _rwaits inv.
Ltac invc_rwaits := _rwaits invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma rwaits_from_nowaits : forall t,
  no_waits t ->
  reserved_waits t.
Proof.
  intros. induction t; invc_nowaits; auto using reserved_waits.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma rwaits_subst : forall x tx t,
  x <> SELF        ->
  no_waits tx      ->
  reserved_waits t ->
  reserved_waits <{[x := tx] t}>.
Proof.
  intros. induction t; invc_rwaits;
  simpl; repeat destruct _str_eq_dec;
  auto using rwaits_from_nowaits, reserved_waits.
Qed.

