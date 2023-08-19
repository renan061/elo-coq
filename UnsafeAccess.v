From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Access.

(* ------------------------------------------------------------------------- *)
(* unsafe-access                                                             *)
(* ------------------------------------------------------------------------- *)

(* There is a mutable pointer to <ad> in the term. *)
Inductive unsafe_access (ad : addr) (m : mem) : tm  -> Prop :=
  | uacc_mem : forall ad' T,
    ad <> ad' ->
    unsafe_access ad m (m[ad'].tm) ->
    unsafe_access ad m <{&ad' :: &T}>

  | uacc_ad : forall T,
    unsafe_access ad m <{&ad :: &T}>

  | uacc_new : forall T t,
    unsafe_access ad m t ->
    unsafe_access ad m <{new T t}>

  | uacc_load : forall t,
    unsafe_access ad m t ->
    unsafe_access ad m <{*t}>

  | uacc_asg1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{t1 = t2}>

  | uacc_asg2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{t1 = t2}>

  | uacc_fun : forall x Tx t,
    unsafe_access ad m t ->
    unsafe_access ad m <{fn x Tx t}>

  | uacc_call1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{call t1 t2}>

  | uacc_call2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{call t1 t2}>

  | uacc_seq1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{t1; t2}>

  | uacc_seq2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{t1; t2}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-access                                                               *)
(* ------------------------------------------------------------------------- *)

Definition safe_access ad m t := access ad m t /\ ~ unsafe_access ad m t.

(* ------------------------------------------------------------------------- *)
(* unfold hints                                                              *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Unfold safe_access : uacc.

#[export] Hint Extern 4 => unfold safe_access : uacc.

(* ------------------------------------------------------------------------- *)
(* unsafe-access inversion                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_uacc tactic :=
  match goal with
  | H : unsafe_access _ _ thread_default |- _ => tactic H
  | H : unsafe_access _ _ <{unit    }>   |- _ => tactic H
  | H : unsafe_access _ _ <{N _     }>   |- _ => tactic H
  | H : unsafe_access _ _ <{& _ :: _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{new _ _ }>   |- _ => tactic H
  | H : unsafe_access _ _ <{* _     }>   |- _ => tactic H
  | H : unsafe_access _ _ <{_ = _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{var _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{fn _ _ _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{call _ _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{_ ; _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{spawn _ }>   |- _ => tactic H
  end.

Ltac inv_uacc := match_uacc inv.

Ltac invc_uacc := match_uacc invc.

(* ------------------------------------------------------------------------- *)
(* not-unsafe-access inversion                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma inv_nuacc_ad_eq : forall m ad T,
  ~ unsafe_access ad m <{&ad :: &T}> ->
  False.
Proof.
  intros. eauto using unsafe_access.
Qed.

Local Lemma inv_nuacc_ad_neq : forall m ad ad' T,
  ~ unsafe_access ad m <{&ad' :: &T}> ->
  (ad <> ad' /\ ~ unsafe_access ad m m[ad'].tm).
Proof.
  intros. destruct (nat_eq_dec ad ad'); subst; eauto using unsafe_access.
  exfalso. eauto using inv_nuacc_ad_eq.
Qed.

Local Ltac solve_nuacc_inversion :=
  intros; try (split; intros); eauto using unsafe_access.

Local Lemma inv_nuacc_new : forall m t ad T,
  ~ unsafe_access ad m <{new T t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_load : forall m t ad,
  ~ unsafe_access ad m <{*t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_asg : forall m t1 t2 ad,
  ~ unsafe_access ad m <{t1 = t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_fun : forall m t ad x Tx,
  ~ unsafe_access ad m <{fn x Tx t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_call : forall m t1 t2 ad,
  ~ unsafe_access ad m <{call t1 t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_seq : forall m t1 t2 ad,
  ~ unsafe_access ad m <{t1; t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Ltac inv_nuacc :=
  match goal with
  | H : ~ unsafe_access ?ad _ <{& ?ad  :: & _}> |- _ =>
    eapply inv_nuacc_ad_eq  in H; solve contradiction
  | H : ~ unsafe_access ?ad _ <{& ?ad' ::   _}> |- _ =>
    eapply inv_nuacc_ad_neq in H as [? ?]
  | H : ~ unsafe_access _ _   <{new _ _      }> |- _ =>
    eapply inv_nuacc_new    in H
  | H : ~ unsafe_access _ _   <{* _          }> |- _ =>
    eapply inv_nuacc_load   in H
  | H : ~ unsafe_access _ _   <{_ = _        }> |- _ =>
    eapply inv_nuacc_asg    in H as [? ?]
  | H : ~ unsafe_access _ _   <{fn _ _ _     }> |- _ =>
    eapply inv_nuacc_fun    in H
  | H : ~ unsafe_access _ _   <{call _ _     }> |- _ =>
    eapply inv_nuacc_call   in H as [? ?]
  | H : ~ unsafe_access _ _   <{_ ; _        }> |- _ =>
    eapply inv_nuacc_seq    in H as [? ?]
  end.

(* ------------------------------------------------------------------------- *)
(* independent properties                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma uacc_dec : forall m t ad,
  Decidable.decidable (unsafe_access ad m t).
Proof. eauto using classic_decidable. Qed.

Theorem uacc_soundness : forall m m' t t' ad e T,
  ad < #m ->
  empty |-- t is T ->
  ~ unsafe_access ad m t ->
  m / t ==[e]==> m' / t' ->
  m[ad].tm = m'[ad].tm.
Proof.
  intros. rename ad into ad'. invc_mstep; trivial.
  - decompose sum (lt_eq_lt_dec ad' (#m)); subst; simpl_array; eauto.
  - decompose sum (lt_eq_lt_dec ad' ad); subst; simpl_array; trivial.
    generalize dependent T. induction_tstep; intros; inv_type; inv_nuacc; eauto.
    inv_type. exfalso. eauto using unsafe_access.
Qed.

Theorem nuacc_from_immutable_type : forall m ad v T,
  value v ->
  empty |-- v is <{{Immut T}}> ->
  unsafe_access ad m v ->
  False.
Proof.
  intros * Hval **.
  destruct Hval; inv_type; inv_uacc; eauto using unsafe_access.
Qed.

Lemma uacc_then_acc : forall m t ad,
  unsafe_access ad m t ->
  access ad m t.
Proof.
  intros * Huacc. induction Huacc; eauto using access.
Qed.

Corollary sacc_then_acc : forall m t ad,
  safe_access ad m t ->
  access ad m t.
Proof.
  intros * [? _]. assumption.
Qed.

Lemma nacc_then_nuacc : forall m t ad,
  ~ access ad m t ->
  ~ unsafe_access ad m t.
Proof.
  intros * ? Huacc. induction Huacc; eauto using access.
Qed.

