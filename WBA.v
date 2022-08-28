From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import Access.

(* -------------------------------------------------------------------------- *)
(* wba_destruct ------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_wba_destruct := 
  intros; unfold well_behaved_access in *;
  match goal with
  | |- _ /\ _ => split
  | |- _ => idtac
  end;
  eauto using access.

Local Lemma wba_destruct_new : forall m t T,
  well_behaved_access m (TM_New T t) ->
  well_behaved_access m t.
Proof. solve_wba_destruct. Qed.

Local Lemma wba_destruct_load : forall m t,
  well_behaved_access m (TM_Load t) ->
  well_behaved_access m t.
Proof. solve_wba_destruct. Qed.

Local Lemma wba_destruct_asg : forall m l r,
  well_behaved_access m (TM_Asg l r) ->
  well_behaved_access m l /\ well_behaved_access m r.
Proof. solve_wba_destruct. Qed.

Local Lemma wba_destruct_fun : forall m x X t,
  well_behaved_access m (TM_Fun x X t) ->
  well_behaved_access m t.
Proof. solve_wba_destruct. Qed.

Local Lemma wba_destruct_call : forall m t1 t2,
  well_behaved_access m (TM_Call t1 t2) ->
  well_behaved_access m t1 /\ well_behaved_access m t2.
Proof. solve_wba_destruct. Qed.

Local Lemma wba_destruct_seq : forall m t1 t2,
  well_behaved_access m (TM_Seq t1 t2) ->
  well_behaved_access m t1 /\ well_behaved_access m t2.
Proof. solve_wba_destruct. Qed.

Ltac destruct_wba :=
  match goal with
    | H : well_behaved_access _ (TM_New _ _)   |- _ =>
        eapply wba_destruct_new in H
    | H : well_behaved_access _ (TM_Load _)  |- _ =>
        eapply wba_destruct_load in H
    | H : well_behaved_access _ (TM_Asg _ _) |- _ => 
        eapply wba_destruct_asg in H as [? ?]
    | H : well_behaved_access _ (TM_Fun _ _ _) |- _ => 
        eapply wba_destruct_fun in H
    | H : well_behaved_access _ (TM_Call _ _) |- _ => 
        eapply wba_destruct_call in H as [? ?]
    | H : well_behaved_access _ (TM_Seq _ _) |- _ => 
        eapply wba_destruct_seq in H as [? ?]
  end.

(* -------------------------------------------------------------------------- *)
(* wba_* -------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Local Lemma wba_new: forall m t T,
  well_behaved_access m t ->
  well_behaved_access m (TM_New T t).
Proof.
  intros. intros ? ?. inversion_access; eauto.
Qed.

Local Lemma wba_load : forall m t,
  well_behaved_access m t ->
  well_behaved_access m (TM_Load t).
Proof.
  intros. intros ? ?. inversion_access; eauto.
Qed.

Local Lemma wba_asg : forall m l r,
  well_behaved_access m l ->
  well_behaved_access m r ->
  well_behaved_access m (TM_Asg l r).
Proof.
  intros. intros ? ?. inversion_access; eauto.
Qed.

Local Lemma wba_fun : forall m x X t,
  well_behaved_access m t ->
  well_behaved_access m (TM_Fun x X t).
Proof.
  intros. intros ? ?. inversion_access; eauto.
Qed.

Local Lemma wba_call : forall m t1 t2,
  well_behaved_access m t1 ->
  well_behaved_access m t2 ->
  well_behaved_access m (TM_Call t1 t2).
Proof.
  intros. intros ? ?. inversion_access; eauto.
Qed.

Local Lemma wba_seq : forall m t1 t2,
  well_behaved_access m t1 ->
  well_behaved_access m t2 ->
  well_behaved_access m (TM_Seq t1 t2).
Proof.
  intros. intros ? ?. inversion_access; eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* mem & subst -------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Local Lemma wba_added_value : forall m v T,
  well_behaved_access (add m v) v ->
  well_behaved_access (add m v) (TM_Ref T (length m)).
Proof.
  intros * ? ? Hacc.
  remember (add m v) as m'.
  remember (TM_Ref T (length m)) as t'.
  induction Hacc; inversion Heqt'; subst.
  - rewrite (get_add_eq TM_Unit) in *; eauto using access.
  - rewrite add_increments_length. lia.
Qed.

Local Lemma wba_stored_value : forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Write ad v]--> t' ->
  well_behaved_access m v.
Proof.
  intros. induction_step; destruct_wba; eauto using access. 
Qed.

Local Lemma wba_mem_add : forall m t v,
  well_behaved_access m t ->
  well_behaved_access (add m v) t.
Proof.
  intros * Hwba ? Hacc. remember (add m v) as m'.
  induction Hacc; subst; try destruct_wba; eauto.
  - eapply IHHacc. intros ad'' Hacc''.
    destruct (lt_eq_lt_dec ad' (length m)) as [[? | ?] | ?]; subst.
    + rewrite (get_add_lt TM_Unit) in *; eauto using access.
    + specialize (Hwba (length m) (access_loc m (length m) _)). lia.
    + rewrite (get_add_gt TM_Unit) in *; eauto. inversion_access.
  - rewrite add_increments_length. eauto using access, Nat.lt_lt_succ_r.
Qed.

Local Lemma wba_mem_set : forall m t ad v,
  well_behaved_access m t ->
  well_behaved_access m v ->
  well_behaved_access (set m ad v) t.
Proof.
  intros * ? ? ? Hacc.
  rewrite set_preserves_length.
  remember (set m ad v) as m'.
  induction Hacc; subst; try destruct_wba; eauto using access.
  eapply IHHacc. destruct (Nat.eq_dec ad ad'); subst.
  - rewrite (get_set_eq TM_Unit); eauto using access.
  - rewrite (get_set_neq TM_Unit) in *; eauto.
    intros ? ?. eauto using access.
Qed.

Local Lemma wba_subst : forall m id t x,
  well_behaved_access m t ->
  well_behaved_access m x ->
  well_behaved_access m ([id := x] t).
Proof.
  intros. induction t; eauto;
  try solve [ destruct_wba
            ; eauto using wba_new, wba_load, wba_asg, wba_call, wba_seq
            ].
  - simpl. destruct String.string_dec; trivial.
  - destruct_wba. simpl. destruct String.string_dec; eauto using wba_fun.
Qed.

(*

(* -------------------------------------------------------------------------- *)
(* preservation ------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Local Lemma none_preservation : forall m t t',
  well_behaved_access m t ->
  t --[EF_None]--> t' ->
  well_behaved_access m t'.
Proof.
  intros. induction_step;
  destruct_wba; eauto using wba_load, wba_asg, wba_fun, wba_call, wba_seq. 
  - admit.
  - destruct_wba. eauto using wba_subst.
Admitted.

Local Lemma alloc_preservation : forall m t t' v,
  well_behaved_access m t ->
  t --[EF_Alloc (length m) v]--> t' ->
  well_behaved_access (add m v) t'.
Proof.
  intros. induction_step; destruct_wba;
  eauto using wba_load, wba_asg, wba_call, wba_seq, wba_mem_add,
              wba_added_value. 
Qed.

Local Lemma load_preservation : forall m t t' ad,
  well_behaved_access m t ->
  t --[EF_Load ad (get TM_Unit m ad)]--> t' ->
  well_behaved_access m t'.
Proof.
  intros. induction_step; destruct_wba;
  eauto using wba_load, wba_asg, wba_call, wba_seq.
  intros ? ?. eauto using access.
Qed.

Local Lemma store_preservation : forall m t t' ad v,
  well_behaved_access m t ->
  t --[EF_Store ad v]--> t' ->
  well_behaved_access (set m ad v) t'.
Proof.
  intros.
  assert (well_behaved_access m v); eauto using wba_stored_value.
  induction_step; destruct_wba;
  eauto using wba_load, wba_asg, wba_call, wba_seq, wba_mem_set.
  intros ? ?. inversion_access.
Qed.

Lemma wba_mstep_preservation : forall m m' t t' eff,
  well_behaved_access m t ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_access m' t'.
Proof.
  intros * ? ?. inversion_mstep;
  eauto using none_preservation, 
    alloc_preservation,
    load_preservation,
    store_preservation.
Qed.

*)
