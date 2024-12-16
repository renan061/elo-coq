From Coq Require Import Lia.
From Coq Require Import List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import ConsistentRegions.
(* ------------------------------------------------------------------------- *)
(* consistent-regions                                                        *)
(* ------------------------------------------------------------------------- *)

Inductive correct_neww : tm -> Prop :=
  | cneww_unit  :                   correct_neww <{unit           }>
  | cneww_nat   : forall n,         correct_neww <{nat n          }>
  | cneww_var   : forall x,         correct_neww <{var x          }>
  | cneww_fun   : forall x Tx t,    correct_neww t   ->
                                    correct_neww <{fn x Tx t      }>
  | cneww_call  : forall t1 t2,     correct_neww t1  ->
                                    correct_neww t2  ->
                                    correct_neww <{call t1 t2     }>
  | cneww_ref   : forall ad T,      correct_neww <{&ad : T        }>
  | cneww_new   : forall t T,       correct_neww t   ->
                                    correct_neww <{new t : T      }>
  | cneww_initR : forall ad t T,    correct_neww t   ->
                                    correct_neww <{init ad t : r&T}>
  | cneww_initX : forall ad t T,    correct_neww t ->
                                    correct_neww <{init ad t : x&T}>
  | cneww_initW : forall ad t T,    correct_neww t   ->
                                    correct_neww <{init ad t : w&T}>
  | cneww_load  : forall t,         correct_neww t   ->
                                    correct_neww <{*t             }>
  | cneww_asg   : forall t1 t2,     correct_neww t1  ->
                                    correct_neww t2  ->
                                    correct_neww <{t1 := t2       }>
  | cneww_acq   : forall t1 x t2,   correct_neww t1  ->
                                    correct_neww t2  ->
                                    correct_neww <{acq t1 x t2    }>
  | cneww_cr    : forall ad t,      correct_neww t ->
                                    correct_neww <{cr ad t        }>
  | cneww_spawn : forall t,         correct_neww t   ->
                                    correct_neww <{spawn t        }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _cneww tt :=
  match goal with
  | H : correct_neww _ _ <{unit        }> |- _ => clear H
  | H : correct_neww _ _ <{nat _       }> |- _ => clear H
  | H : correct_neww _ _ <{var _       }> |- _ => clear H
  | H : correct_neww _ _ <{fn _ _ _    }> |- _ => tt H
  | H : correct_neww _ _ <{call _ _    }> |- _ => tt H
  | H : correct_neww _ _ <{& _ : _     }> |- _ => tt H
  | H : correct_neww _ _ <{new _ : _   }> |- _ => tt H
  | H : correct_neww _ _ <{init _ _ : _}> |- _ => tt H
  | H : correct_neww _ _ <{* _         }> |- _ => tt H
  | H : correct_neww _ _ <{_ := _      }> |- _ => tt H
  | H : correct_neww _ _ <{acq _ _ _   }> |- _ => tt H
  | H : correct_neww _ _ <{cr _ _      }> |- _ => tt H
  | H : correct_neww _ _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_cneww  := _cneww inv.
Ltac invc_cneww := _cneww invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma cneww_creg_relation : forall o s R1 R2 t,
  consistent_regions o R1 t -> 
  correct_neww   s R2 t ->
  R1 = R2.
Proof.
  intros. gendep o. gendep s.
  induction t; intros;
  try solve [invc_creg; invc_cneww; eauto].
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - invc_creg. invc_cneww. eapply IHt.
    +
Qed.

