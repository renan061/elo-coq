From Elo Require Import Core.

From Elo Require Import AccessCore.

From Elo Require Import Properties1.
From Elo Require Import Properties2.

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

(* preservation lemmas ----------------------------------------------------- *)

Lemma nacc_mem_set1 : forall ad ad' m t t',
  ~ access ad m t' ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad m[ad'.t <- t'] t.
Proof.
  intros ** Hacc. induction Hacc; upsilon; eauto using access.
Qed.

Lemma nacc_mem_set2 : forall ad ad' m t t',
  ~ access ad' m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad m[ad'.t <- t'] t.
Proof.
  intros ** Hacc. induction Hacc; repeat invc_nacc; upsilon; eauto.
Qed.

(* preservation ------------------------------------------------------------ *)

(*

Definition unique_initializers (m : mem) (ths : threads) := forall ad,
  ad < #m ->
  (m[ad].t <> None -> forall_threads ths (no_init ad)) /\
  (m[ad].t =  None -> forone_thread  ths (one_init ad) (no_init ad)).

Definition unique_critical_regions (m : mem) (ths : threads) := forall ad,
  (m[ad].X = false -> forall_threads ths (no_cr ad)) /\
  (m[ad].X = true  -> forone_thread  ths (one_cr ad) (no_cr ad)).

From unique_initializers:
  forone_thread ths (one_init ad) (no_init ad))

From init_cr_exclusivity: 
  (one_init ad ths[tid1] -> no_cr ad ths[tid2])

*)

Corollary oneinit_or_noinit_from_ui : forall ad m ths tid,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  unique_initializers m ths ->
  m[ad].t = None ->
  (one_init ad ths[tid]) \/ (no_init ad ths[tid]).
Proof.
  intros until 1. intros Hui Had.
  lt_eq_gt ad (#m); eauto using noinit_from_vad1, noinit_from_vad2.
  specialize (Hui ad). aspecialize. specialize Hui as [_ Hnone].
  specialize (Hnone Had) as [tid' [Hone Hno]].
  destruct (nat_eq_dec tid' tid); subst; auto.
Qed.

Corollary noinit_from_ui : forall ad m ths tid,
  forall_threads ths (valid_addresses m) ->
  (* --- *)
  unique_initializers m ths ->
  m[ad].t <> None ->
  (one_init ad ths[tid]) \/ (no_init ad ths[tid]).
Proof.
  intros until 1. intros Hui Had.
  lt_eq_gt ad (#m); eauto using noinit_from_vad1, noinit_from_vad2.
  specialize (Hui ad). aspecialize. specialize Hui as [Hsome _].
  aspecialize. auto.
Qed.



Lemma oneinit_or_onecr_from_xacc : forall adx ad m t,
  xaccess adx ad m t ->
  (one_init adx t) \/ (one_cr adx t).
Proof.
  intros.
Abort.

Lemma nacc_preservation_write : forall ad ad' m t' t1 t2,
  consistent_inits m t1 ->
  (* --- *)
  ~ access ad m t1 ->
  t1 --[e_write ad' t']--> t2 ->
  ~ access ad m[ad'.t <- t'] t2.
Proof.
  intros. ind_tstep; invc_ci; invc_nacc; eauto with not_access;
  repeat aspecialize.
  - admit.
  - admit.
  - destruct (acc_dec ad m t'); eauto using nacc_mem_set1 with not_access.
    destruct (acc_dec ad' m t2); eauto using nacc_mem_set2 with not_access.
    (* acc_or_xacc_from_write => *)
    assert (access ad' m t1 \/ (exists adx, xaccess adx ad' m t1)) as [? | ?]
      by admit.
    +
    intros ?.
    admit.
Abort.
