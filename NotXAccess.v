From Elo Require Import Core.

From Elo Require Import AccessCore.

(* ------------------------------------------------------------------------- *)
(* not-xaccess                                                               *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_cons_nxacc := 
  intros ** ?; try invc_xacc; try invc_eq; eauto using xaccess.

Lemma nxacc_unit : forall adx ad m,
  ~ xaccess adx ad m <{unit}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_nat : forall adx ad m n,
  ~ xaccess adx ad m <{nat n}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_var : forall adx ad m x,
  ~ xaccess adx ad m <{var x}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_fun : forall adx ad m x Tx t,
  ~ xaccess adx ad m t ->
  ~ xaccess adx ad m <{fn x Tx t}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_call : forall adx ad m t1 t2,
  ~ xaccess adx ad m t1 ->
  ~ xaccess adx ad m t2 ->
  ~ xaccess adx ad m <{call t1 t2}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_refR : forall adx ad ad' m T,
  ~ xaccess adx ad m <{&ad' : r&T}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_refX : forall adx ad ad' m T,
  ~ xaccess adx ad m <{&ad' : x&T}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_refW : forall adx ad ad' m T,
  ~ xaccess adx ad m <{&ad' : w&T}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_new : forall adx ad m t T,
  ~ xaccess adx ad m t ->
  ~ xaccess adx ad m <{new t : T}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_initR : forall adx adx' ad m t T,
  ~ xaccess adx ad m t ->
  ~ xaccess adx ad m <{init adx' t : r&T}>.
Proof. solve_cons_nxacc. Qed.

(* nxacc_initX *)

Lemma nxacc_initW : forall adx adx' ad m t T,
  ~ xaccess adx ad m t ->
  ~ xaccess adx ad m <{init adx' t : w&T}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_load : forall adx ad m t,
  ~ xaccess adx ad m t ->
  ~ xaccess adx ad m <{*t}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_asg : forall adx ad m t1 t2,
  ~ xaccess adx ad m t1 ->
  ~ xaccess adx ad m t2 ->
  ~ xaccess adx ad m <{t1 := t2}>.
Proof. solve_cons_nxacc. Qed.

Lemma nxacc_acq : forall adx ad m t1 t2,
  ~ xaccess adx ad m t1 ->
  ~ xaccess adx ad m t2 ->
  ~ xaccess adx ad m <{acq t1 t2}>.
Proof. solve_cons_nxacc. Qed.

(* nxacc_cr *)

Lemma nxacc_spawn : forall adx ad m t,
  ~ xaccess adx ad m <{spawn t}>.
Proof. solve_cons_nxacc. Qed.

#[export] Hint Resolve
  nxacc_unit  nxacc_nat
  nxacc_var   nxacc_fun         nxacc_call
  nxacc_refR  nxacc_refX        nxacc_refW
  nxacc_new   nxacc_load        nxacc_asg
  nxacc_initR (* nxacc_initX *) nxacc_initW
  nxacc_acq   (* nxacc_cr    *)
  nxacc_spawn
  : not_xaccess.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_nxacc := 
  intros; try split; eauto using xaccess.

Local Lemma inv_nxacc_fun : forall adx ad m x Tx t,
  ~ xaccess adx ad m <{fn x Tx t}> ->
  ~ xaccess adx ad m t.
Proof. solve_inv_nxacc. Qed.

Local Lemma inv_nxacc_call : forall adx ad m t1 t2,
  ~ xaccess adx ad m <{call t1 t2}> ->
  ~ xaccess adx ad m t1 /\ ~ xaccess adx ad m t2.
Proof. solve_inv_nxacc. Qed.

Local Lemma inv_nxacc_new : forall adx ad m t T,
  ~ xaccess adx ad m <{new t : T}> ->
  ~ xaccess adx ad m t.
Proof. solve_inv_nxacc. Qed.

Local Lemma inv_nxacc_initR : forall adx ad ad' m t T,
  ~ xaccess adx ad m <{init ad' t : r&T}> ->
  ~ xaccess adx ad m t.
Proof. solve_inv_nxacc. Qed.

Local Lemma inv_nxacc_initX : forall adx adx' ad m t T,
  ~ xaccess adx ad m <{init adx' t : x&T}> ->
  (adx' = adx /\ ~ access ad m t) \/ (adx' <> adx /\ ~ xaccess adx ad m t).
Proof.
  intros. destruct (nat_eq_dec adx' adx); subst;
  unfold not in *; eauto using xaccess.
Qed.

Local Lemma inv_nxacc_initW : forall adx ad ad' m t T,
  ~ xaccess adx ad m <{init ad' t : w&T}> ->
  ~ xaccess adx ad m t.
Proof. solve_inv_nxacc. Qed.

Local Lemma inv_nxacc_load : forall adx ad m t,
  ~ xaccess adx ad m <{*t}> ->
  ~ xaccess adx ad m t.
Proof. solve_inv_nxacc. Qed.

Local Lemma inv_nxacc_asg : forall adx ad m t1 t2,
  ~ xaccess adx ad m <{t1 := t2}> ->
  ~ xaccess adx ad m t1 /\ ~ xaccess adx ad m t2.
Proof. solve_inv_nxacc. Qed.

Local Lemma inv_nxacc_acq : forall adx ad m t1 t2,
  ~ xaccess adx ad m <{acq t1 t2}> ->
  ~ xaccess adx ad m t1 /\ ~ xaccess adx ad m t2.
Proof. solve_inv_nxacc. Qed.

Local Lemma inv_nxacc_cr : forall adx adx' ad m t,
  ~ xaccess adx ad m <{cr adx' t}> ->
  (adx' = adx /\ ~ access ad m t) \/ (adx' <> adx /\ ~ xaccess adx ad m t).
Proof.
  intros. destruct (nat_eq_dec adx' adx); subst;
  unfold not in *; eauto using xaccess.
Qed.

Ltac invc_nxacc :=
match goal with
  | H : ~ xaccess _ _ _ <{unit          }> |- _ => clear H
  | H : ~ xaccess _ _ _ <{nat _         }> |- _ => clear H
  | H : ~ xaccess _ _ _ <{var _         }> |- _ => clear H
  | H : ~ xaccess _ _ _ <{fn _ _ _      }> |- _ =>
      eapply inv_nxacc_fun   in H
  | H : ~ xaccess _ _ _ <{call _ _      }> |- _ => 
      eapply inv_nxacc_call  in H as [? ?]
  | H : ~ xaccess _ _ _ <{& _ : _       }> |- _ => clear H
  | H : ~ xaccess _ _ _ <{new _ : _     }> |- _ =>
      eapply inv_nxacc_new   in H
  | H : ~ xaccess _ _ _ <{init _ _ : r&_}> |- _ =>
      eapply inv_nxacc_initR in H
  | H : ~ xaccess _ _ _ <{init _ _ : x&_}> |- _ =>
      eapply inv_nxacc_initX in H as [[? ?] | [? ?]]; subst
  | H : ~ xaccess _ _ _ <{init _ _ : w&_}> |- _ =>
      eapply inv_nxacc_initW in H
  | H : ~ xaccess _ _ _ <{* _           }> |- _ =>
      eapply inv_nxacc_load  in H
  | H : ~ xaccess _ _ _ <{_ := _        }> |- _ =>
      eapply inv_nxacc_asg   in H as [? ?]
  | H : ~ xaccess _ _ _ <{acq _ _       }> |- _ =>
      eapply inv_nxacc_acq   in H as [? ?]
  | H : ~ xaccess _ _ _ <{cr _ _        }> |- _ =>
      eapply inv_nxacc_cr    in H as [[? ?] | [? ?]]; subst
  | H : ~ xaccess _ _ _ <{spawn _       }> |- _ => clear H
end.

