From Elo Require Import Core.

From Elo Require Import AccessCore.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_cons_nacc := 
  intros ** ?; invc_acc; try invc_eq; eauto.

Lemma nacc_unit : forall ad m,
  ~ access ad m <{unit}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_nat : forall ad m n,
  ~ access ad m <{nat n}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_var : forall ad m x,
  ~ access ad m <{var x}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_fun : forall ad m x Tx t,
  ~ access ad m t ->
  ~ access ad m <{fn x Tx t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_call : forall ad m t1 t2,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{call t1 t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_refR : forall m ad ad' t T,
  ad <> ad' ->
  m[ad'].t = Some t ->
  ~ access ad m t ->
  ~ access ad m <{&ad' : r&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_refX : forall m ad ad' T,
  ~ access ad m <{&ad' : x&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_refW : forall m ad ad' t T,
  ad <> ad' ->
  m[ad'].t = Some t ->
  ~ access ad m t ->
  ~ access ad m <{&ad' : w&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_new : forall ad m t T,
  ~ access ad m t ->
  ~ access ad m <{new t : T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_initR : forall adx ad m t T,
  ~ access ad m t ->
  ~ access ad m <{init adx t : r&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_initX : forall adx ad m t T,
  ~ access ad m <{init adx t : x&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_initW : forall adx ad m t T,
  ~ access ad m t ->
  ~ access ad m <{init adx t : w&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_load : forall ad m t,
  ~ access ad m t ->
  ~ access ad m <{*t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_asg : forall ad m t1 t2,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{t1 := t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_acq : forall ad m t1 t2,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{acq t1 t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_cr : forall ad m adx t,
  ~ access ad m <{cr adx t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_spawn : forall ad m t,
  ~ access ad m <{spawn t}>.
Proof. solve_cons_nacc. Qed.

#[export] Hint Resolve
  nacc_unit  nacc_nat
  nacc_var   nacc_fun   nacc_call
  nacc_refR  nacc_refX  nacc_refW
  nacc_new   nacc_load  nacc_asg
  nacc_initR nacc_initX nacc_initW
  nacc_acq   nacc_cr
  nacc_spawn
  : not_access.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_nacc := 
  intros; try split; eauto using access.

Local Lemma inv_nacc_fun : forall m x Tx t ad,
  ~ access ad m <{fn x Tx t}> ->
  ~ access ad m t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_call : forall m t1 t2 ad,
  ~ access ad m <{call t1 t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_refR : forall m ad ad' T,
  ~ access ad m <{&ad' : r&T}> ->
  ad <> ad' /\ (forall t, m[ad'].t = Some t -> ~ access ad m t).
Proof.
  intros. assert (ad <> ad') by (intros ?; subst; eauto using access).
  split; eauto using access.
Qed.

Local Lemma inv_nacc_refW : forall m ad ad' T,
  ~ access ad m <{&ad' : w&T}> ->
  ad <> ad' /\ (forall t, m[ad'].t = Some t -> ~ access ad m t).
Proof.
  intros. assert (ad <> ad') by (intros ?; subst; eauto using access).
  split; eauto using access.
Qed.

Local Lemma inv_nacc_new : forall m t ad T,
  ~ access ad m <{new t : T}> ->
  ~ access ad m t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_initR : forall m ad ad' t T,
  ~ access ad m <{init ad' t : r&T}> ->
  ~ access ad m t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_initW : forall m ad ad' t T,
  ~ access ad m <{init ad' t : w&T}> ->
  ~ access ad m t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_load : forall m t ad,
  ~ access ad m <{*t}> ->
  ~ access ad m t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_asg : forall m t1 t2 ad,
  ~ access ad m <{t1 := t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_acq : forall m t1 t2 ad,
  ~ access ad m <{acq t1 t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_inv_nacc. Qed.

Ltac invc_nacc :=
match goal with
| H: ~ access _ _ <{unit          }> |- _ => clear H
| H: ~ access _ _ <{nat _         }> |- _ => clear H
| H: ~ access _ _ <{var _         }> |- _ => clear H
| H: ~ access _ _ <{fn _ _ _      }> |- _ => eapply inv_nacc_fun   in H
| H: ~ access _ _ <{call _ _      }> |- _ => eapply inv_nacc_call  in H as [? ?]
| H: ~ access _ _ <{& _ : r&_     }> |- _ => eapply inv_nacc_refR  in H as [? ?]
| H: ~ access _ _ <{& _ : x&_     }> |- _ => clear H
| H: ~ access _ _ <{& _ : w&_     }> |- _ => eapply inv_nacc_refW  in H as [? ?]
| H: ~ access _ _ <{& _ : _       }> |- _ => idtac H
| H: ~ access _ _ <{new _ : _     }> |- _ => eapply inv_nacc_new   in H
| H: ~ access _ _ <{init _ _ : r&_}> |- _ => eapply inv_nacc_initR in H
| H: ~ access _ _ <{init _ _ : x&_}> |- _ => clear H
| H: ~ access _ _ <{init _ _ : w&_}> |- _ => eapply inv_nacc_initW in H
| H: ~ access _ _ <{init _ _ : _  }> |- _ => idtac H
| H: ~ access _ _ <{* _           }> |- _ => eapply inv_nacc_load  in H
| H: ~ access _ _ <{_ := _        }> |- _ => eapply inv_nacc_asg   in H as [? ?]
| H: ~ access _ _ <{acq _ _       }> |- _ => eapply inv_nacc_acq   in H as [? ?]
| H: ~ access _ _ <{cr _ _        }> |- _ => clear H
| H: ~ access _ _ <{spawn _       }> |- _ => clear H
end.

