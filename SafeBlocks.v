From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import Access.
From Elo Require Import UnsafeAccess.

(* -------------------------------------------------------------------------- *)
(* TODO                                                                       *)
(* -------------------------------------------------------------------------- *)

Inductive AllMutRefs (ad : addr) : tm -> Prop :=
  | amr_unit :
    AllMutRefs ad <{ unit }>

  | amr_num : forall n,
    AllMutRefs ad <{ N n }>

  | amr_ref : forall T,
    AllMutRefs ad <{ &ad :: &T }>

  | amr_new : forall t T,
    AllMutRefs ad t ->
    AllMutRefs ad <{ new T t }>

  | amr_load : forall t,
    AllMutRefs ad t ->
    AllMutRefs ad <{ *t }>

  | amr_asg : forall t1 t2,
    AllMutRefs ad t1 ->
    AllMutRefs ad t2 ->
    AllMutRefs ad <{ t1 = t2 }>

  | amr_var : forall x,
    AllMutRefs ad <{ var x }>

  | amr_fun : forall t x Tx,
    AllMutRefs ad t ->
    AllMutRefs ad <{ fn x Tx --> t }>

  | amr_call : forall t1 t2,
    AllMutRefs ad t1 ->
    AllMutRefs ad t2 ->
    AllMutRefs ad <{ call t1 t2 }>
    
  | amr_seq : forall t1 t2,
    AllMutRefs ad t1 ->
    AllMutRefs ad t2 ->
    AllMutRefs ad <{ t1; t2 }>

  | amr_spawn : forall t,
    AllMutRefs ad t ->
    AllMutRefs ad <{ spawn t }>
  .

Inductive AllMutRefsMem (ad : addr) : mem -> Prop :=
  | amrm_nil :
    AllMutRefsMem ad nil

  | amrm_cons_unit : forall m,
    AllMutRefsMem ad m ->
    AllMutRefsMem ad (cons <{ unit }> m)

  | amrm_cons_num : forall m n,
    AllMutRefsMem ad m ->
    AllMutRefsMem ad (cons <{ N n }> m)

  | amrm_cons_refI : forall m ad' T,
    AllMutRefsMem ad m ->
    ad <> ad' ->
    AllMutRefsMem ad (cons <{ &ad' :: i&T }> m)

  | amrm_cons_refM1 : forall m T ad',
    AllMutRefsMem ad m ->
    ad <> ad' ->
    AllMutRefsMem ad (cons <{ &ad' :: &T }> m)

  | amrm_cons_refM2 : forall m T,
    AllMutRefsMem ad m ->
    AllMutRefsMem ad (cons <{ &ad :: &T }> m)

  | amrm_cons_fun : forall m t x Tx,
    AllMutRefs ad t ->
    AllMutRefsMem ad m ->
    AllMutRefsMem ad (cons <{ fn x Tx --> t }> m)
  .


(* -------------------------------------------------------------------------- *)
(* contains-block                                                             *)
(* -------------------------------------------------------------------------- *)

Reserved Notation " t 'contains_block' t' " (at level 30, no associativity).

Inductive ContainsBlock : tm -> tm -> Prop :=
  | contains_block_new : forall t t' T,
    t contains_block t' ->
    <{ new T t }> contains_block t'

  | contains_block_load : forall t t',
    t contains_block t' ->
    <{ *t }> contains_block t'

  | contains_block_asg1 : forall t1 t2 t',
    t1 contains_block t' ->
    <{ t1 = t2 }> contains_block t'

  | contains_block_asg2 : forall t1 t2 t',
    t2 contains_block t' ->
    <{ t1 = t2 }> contains_block t'

  | contains_block_fun : forall t t' x Tx,
    t contains_block t' ->
    <{ fn x Tx --> t }> contains_block t'

  | contains_block_call1 : forall t1 t2 t',
    t1 contains_block t' ->
    <{ call t1 t2 }> contains_block t'

  | contains_block_call2 : forall t1 t2 t',
    t2 contains_block t' ->
    <{ call t1 t2 }> contains_block t'

  | contains_block_seq1 : forall t1 t2 t',
    t1 contains_block t' ->
    <{ t1; t2 }> contains_block t'

  | contains_block_seq2 : forall t1 t2 t',
    t2 contains_block t' ->
    <{ t1; t2 }> contains_block t'

  | contains_block_spawn : forall t t',
    t <> t' ->
    t contains_block t' ->
    <{ spawn t }> contains_block t'

  | contains_block_eq : forall block,
    <{ spawn block }> contains_block block 

  where "t 'contains_block' t'" := (ContainsBlock t t').

Lemma step_spawn_contains_block : forall t t' block,
  t --[EF_Spawn block]--> t' ->
  t contains_block block.
Proof.
  intros. induction_step; eauto using ContainsBlock.
Qed.

Lemma conblock_dec : forall t t',
  Decidable.decidable (t contains_block t').
Proof.
  intros. induction t;
  try solve [right; intros F; inversion F].
  - destruct IHt.
    + left. eauto using ContainsBlock.
    + right. intros F. inversion F; subst. contradiction.
  - destruct IHt.
    + left. eauto using ContainsBlock.
    + right. intros F. inversion F; subst. contradiction.
  - destruct IHt1, IHt2.
    + left. eauto using ContainsBlock.
    + left. eauto using ContainsBlock.
    + left. eauto using ContainsBlock.
    + right. intros F. inversion F; subst; contradiction.
  - destruct IHt.
    + left. eauto using ContainsBlock.
    + right. intros F. inversion F; subst. contradiction.
  - destruct IHt1, IHt2.
    + left. eauto using ContainsBlock.
    + left. eauto using ContainsBlock.
    + left. eauto using ContainsBlock.
    + right. intros F. inversion F; subst; contradiction.
  - destruct IHt1, IHt2.
    + left. eauto using ContainsBlock.
    + left. eauto using ContainsBlock.
    + left. eauto using ContainsBlock.
    + right. intros F. inversion F; subst; contradiction.
  - destruct IHt.
    + left. destruct (tm_eq_dec t t'); subst; eauto using ContainsBlock.
    + right. intros F. inversion F; subst.
      * contradiction.
      * inversion F; subst.
        ** contradiction.
        ** admit.
Abort.

Lemma conblock_dec : forall t t',
  Decidable.decidable (t contains_block t').
Proof.
  intros. eauto using classic_decidable.
Qed.

(* -------------------------------------------------------------------------- *)
(* safe-blocks                                                                *)
(* -------------------------------------------------------------------------- *)

Definition SafeBlocks (m : mem) (t : tm) := forall block ad,
  access m t ad ->
  t contains_block block ->
  access m block ad ->
  ~ UnsafeAccess m t ad.

(* -------------------------------------------------------------------------- *)
(* constructor-sb                                                             *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_sb_con :=
  intros * Hsb; intros ? ? ? H ? ?;
  inversion_access; inversion_subst_clear H; inversion_uacc;
  eapply Hsb; eauto.

Local Lemma sb_con_new : forall m t T,
  SafeBlocks m t ->
  SafeBlocks m <{ new T t }>.
Proof. solve_sb_con. Qed.

Local Lemma sb_con_load : forall m t,
  SafeBlocks m t ->
  SafeBlocks m <{ *t }>.
Proof. solve_sb_con. Qed.

Local Lemma sb_con_asg: forall m t1 t2 T,
  empty |-- t1 is <{{ & T }}> ->
  empty |-- t2 is T ->
  SafeBlocks m t1 ->
  SafeBlocks m t2 ->
  SafeBlocks m <{ t1 = t2 }>.
Proof.
  intros * Htype1 Htyp2 Hsb1 Hsb2. intros ? ? Hacc Hcon Hblock Huacc.
  inversion_access; inversion_subst_clear Hcon; inversion_uacc;
  try solve [eapply Hsb1; eauto];
  try solve [eapply Hsb2; eauto].
  - assert (access m t2 ad) by eauto using uacc_then_acc.
    destruct (conblock_dec t2 block).
    + specialize (Hsb2 block ad) as ?.
      do 3 auto_specialize. contradiction.
    + specialize (Hsb1 block ad H2 H3 Hblock) as ?.
    
    destruct (uacc_dec m t1 ad); try solve [eapply Hsb1; eauto].
    eapply Hsb1; eauto.
Abort.

(* -------------------------------------------------------------------------- *)
(* inversion-sb                                                               *)
(* -------------------------------------------------------------------------- *)

Local Ltac solve_inv_sb :=
  intros * H; try split; intros ? ? ? ? ? ?;
  eapply H; eauto using access, UnsafeAccess, ContainsBlock.

Local Lemma sb_inv_new : forall m t T,
  SafeBlocks m <{ new T t }> ->
  SafeBlocks m t.
Proof. solve_inv_sb. Qed.

Local Lemma sb_inv_load : forall m t,
  SafeBlocks m <{ *t }> ->
  SafeBlocks m t.
Proof. solve_inv_sb. Qed.

Local Lemma sb_inv_asg : forall m t1 t2,
  SafeBlocks m <{ t1 = t2 }> ->
  (SafeBlocks m t1) /\ (SafeBlocks m t2).
Proof. solve_inv_sb. Qed.

Local Lemma sb_inv_fun : forall m t x Tx,
  SafeBlocks m <{ fn x Tx --> t }> ->
  SafeBlocks m t.
Proof. solve_inv_sb. Qed.

Local Lemma sb_inv_call : forall m t1 t2,
  SafeBlocks m <{ call t1 t2 }> ->
  (SafeBlocks m t1) /\ (SafeBlocks m t2).
Proof. solve_inv_sb. Qed.

Local Lemma sb_inv_seq : forall m t1 t2,
  SafeBlocks m <{ t1; t2 }> ->
  (SafeBlocks m t1) /\ (SafeBlocks m t2).
Proof. solve_inv_sb. Qed.

Ltac inversion_sb :=
  match goal with
  | H: SafeBlocks _ <{ new _ _      }> |- _ => eapply sb_inv_new  in H
  | H: SafeBlocks _ <{ * _          }> |- _ => eapply sb_inv_load in H
  | H: SafeBlocks _ <{ _ = _        }> |- _ => eapply sb_inv_asg  in H as [? ?]
  | H: SafeBlocks _ <{ fn _ _ --> _ }> |- _ => eapply sb_inv_fun  in H
  | H: SafeBlocks _ <{ call _ _     }> |- _ => eapply sb_inv_call in H as [? ?]
  | H: SafeBlocks _ <{ _ ; _        }> |- _ => eapply sb_inv_seq  in H as [? ?]
  end.

(* -------------------------------------------------------------------------- *)
(* safe-blocks-preservation                                                   *)
(* -------------------------------------------------------------------------- *)

Local Lemma step_none_sb_preservation : forall m t t' T,
  empty |-- t is T ->
  SafeBlocks m t ->
  t --[EF_None]--> t' ->
  SafeBlocks m t'.
Proof.
  intros. generalize dependent T.
  induction_step; intros; inversion_type; inversion_sb;
  eauto using sb_con_new, sb_con_load.
  - do 2 auto_specialize. specialize (IHstep (<{{ &T0 }}>)). auto_specialize.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.





