From Elo Require Import Core.

From Elo Require Import AccessCore.

From Elo Require Import Properties1.
From Elo Require Import Properties2.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_cons_nacc := 
  intros ** ?; invc_acc; try invc_eq; eauto.

Lemma nacc_unit : forall ad,
  ~ access ad <{unit}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_nat : forall ad n,
  ~ access ad <{nat n}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_var : forall ad x,
  ~ access ad <{var x}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_fun : forall ad x Tx t,
  ~ access ad t ->
  ~ access ad <{fn x Tx t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_call : forall ad t1 t2,
  ~ access ad t1 ->
  ~ access ad t2 ->
  ~ access ad <{call t1 t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_refR : forall ad ad' T,
  ad <> ad' ->
  ~ access ad <{&ad' : r&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_refX : forall ad ad' T,
  ~ access ad <{&ad' : x&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_refW : forall ad ad' T,
  ad <> ad' ->
  ~ access ad <{&ad' : w&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_new : forall ad t T,
  ~ access ad t ->
  ~ access ad <{new t : T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_initR : forall adx ad t T,
  ~ access ad t ->
  ~ access ad <{init adx t : r&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_initX : forall adx ad t T,
  ~ access ad <{init adx t : x&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_initW : forall adx ad t T,
  ~ access ad t ->
  ~ access ad <{init adx t : w&T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_load : forall ad t,
  ~ access ad t ->
  ~ access ad <{*t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_asg : forall ad t1 t2,
  ~ access ad t1 ->
  ~ access ad t2 ->
  ~ access ad <{t1 := t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_acq : forall ad t1 t2,
  ~ access ad t1 ->
  ~ access ad t2 ->
  ~ access ad <{acq t1 t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_cr : forall ad adx t,
  ~ access ad <{cr adx t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_spawn : forall ad t,
  ~ access ad <{spawn t}>.
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

Local Lemma inv_nacc_fun : forall x Tx t ad,
  ~ access ad <{fn x Tx t}> ->
  ~ access ad t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_call : forall t1 t2 ad,
  ~ access ad <{call t1 t2}> ->
  ~ access ad t1 /\ ~ access ad t2.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_refR : forall ad ad' T,
  ~ access ad <{&ad' : r&T}> ->
  ad <> ad'.
Proof.
  intros ** ?. subst. eauto using access.
Qed.

Local Lemma inv_nacc_refW : forall ad ad' T,
  ~ access ad <{&ad' : w&T}> ->
  ad <> ad'.
Proof.
  intros ** ?. subst. eauto using access.
Qed.

Local Lemma inv_nacc_new : forall t ad T,
  ~ access ad <{new t : T}> ->
  ~ access ad t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_initR : forall ad ad' t T,
  ~ access ad <{init ad' t : r&T}> ->
  ~ access ad t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_initW : forall ad ad' t T,
  ~ access ad <{init ad' t : w&T}> ->
  ~ access ad t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_load : forall t ad,
  ~ access ad <{*t}> ->
  ~ access ad t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_asg : forall t1 t2 ad,
  ~ access ad <{t1 := t2}> ->
  ~ access ad t1 /\ ~ access ad t2.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_acq : forall t1 t2 ad,
  ~ access ad <{acq t1 t2}> ->
  ~ access ad t1 /\ ~ access ad t2.
Proof. solve_inv_nacc. Qed.

Ltac invc_nacc :=
match goal with
| H: ~ access _ <{unit          }> |- _ => clear H
| H: ~ access _ <{nat _         }> |- _ => clear H
| H: ~ access _ <{var _         }> |- _ => clear H
| H: ~ access _ <{fn _ _ _      }> |- _ => eapply inv_nacc_fun   in H
| H: ~ access _ <{call _ _      }> |- _ => eapply inv_nacc_call  in H as [? ?]
| H: ~ access _ <{& _ : r&_     }> |- _ => eapply inv_nacc_refR  in H
| H: ~ access _ <{& _ : x&_     }> |- _ => clear H
| H: ~ access _ <{& _ : w&_     }> |- _ => eapply inv_nacc_refW  in H
| H: ~ access _ <{& _ : _       }> |- _ => idtac H
| H: ~ access _ <{new _ : _     }> |- _ => eapply inv_nacc_new   in H
| H: ~ access _ <{init _ _ : r&_}> |- _ => eapply inv_nacc_initR in H
| H: ~ access _ <{init _ _ : x&_}> |- _ => clear H
| H: ~ access _ <{init _ _ : w&_}> |- _ => eapply inv_nacc_initW in H
| H: ~ access _ <{init _ _ : _  }> |- _ => idtac H
| H: ~ access _ <{* _           }> |- _ => eapply inv_nacc_load  in H
| H: ~ access _ <{_ := _        }> |- _ => eapply inv_nacc_asg   in H as [? ?]
| H: ~ access _ <{acq _ _       }> |- _ => eapply inv_nacc_acq   in H as [? ?]
| H: ~ access _ <{cr _ _        }> |- _ => clear H
| H: ~ access _ <{spawn _       }> |- _ => clear H
end.

(* preservation ------------------------------------------------------------ *)

(* TODO *)
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

(* TODO *)
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

Lemma oneinit_or_onecr_from_xacc : forall adx ad t,
  xaccess adx ad t ->
  (one_init adx t) \/ (one_cr adx t).
Proof.
  intros.
Abort.

Lemma nacc_preservation_write : forall ad ad' t' t1 t2,
  ~ access ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  ~ access ad t2.
Proof.
  intros. ind_tstep; invc_nacc; eauto with not_access.
  eapply nacc_init.
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
