From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* memtyp & uacc/sacc                                                        *)
(* ------------------------------------------------------------------------- *)

(* If there is access:
   The access is unsafe if and only if the memtyp is mutable.
*)
Lemma memtyp_mut_iff_uacc : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  access ad m t ->
  (* --- *)
  unsafe_access ad m t <-> (exists T, m[ad].typ = <{{&T}}>).
Proof.
  intros * ? ? ? Hacc. split.
  - intros Huacc. clear Hacc. induction Huacc; inv_ctr; eauto.
  - intros [? Heq]. induction Hacc; inv_ctr; eauto using unsafe_access.
    + exfalso. eauto using nuacc_from_immutable_type.
    + rewrite Heq in *. discriminate.
Qed.

(* If one access to an address is unsafe,
   then all accesses to that address are unsafe.
*)
Corollary uacc_by_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  consistently_typed_references m t' ->
  (* --- *)
  access ad m t ->
  unsafe_access ad m t' ->
  unsafe_access ad m t.
Proof.
  intros.
  eapply memtyp_mut_iff_uacc; eauto.
  eapply memtyp_mut_iff_uacc; eauto using uacc_then_acc.
Qed.

(* If there is access:
   The access is safe if and only if the memtyp is immutable.
*)
Lemma memtyp_immut_iff_sacc : forall m t ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  access ad m t ->
  (* --- *)
  safe_access ad m t <-> (exists T, m[ad].typ = <{{i&T}}>).
Proof.
  intros * Hval ? ? Hacc. split.
  - intros [? ?]. induction Hacc; invc_ctr; eauto; try inv_nuacc; eauto.
    eapply IHHacc; eauto. intros ?. destruct (Hval ad'); inv_type; inv_uacc.
  - intros [? Heq]; split; trivial.
    induction Hacc; intros ?; invc_ctr; inv_uacc; eauto;
    try (eapply IHHacc; eauto using uacc_by_association).
    rewrite Heq in *. discriminate.
Qed.

(* If one access to an address is safe,
   then all accesses to that address are safe.
*)
Corollary sacc_by_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (consistently_typed_references m) ->
  consistently_typed_references m t ->
  consistently_typed_references m t' ->
  (* --- *)
  access ad m t ->
  safe_access ad m t' ->
  safe_access ad m t.
Proof.
  intros * ? ? ? ? ? Hsacc.
  eapply memtyp_immut_iff_sacc; eauto.
  specialize Hsacc as Hsacc'. destruct Hsacc' as [? ?].
  eapply memtyp_immut_iff_sacc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* memtyp preservation                                                       *)
(* ------------------------------------------------------------------------- *)

Module MemExt.
  Reserved Infix "extends" (at level 20, no associativity).

  Inductive extension : mem -> mem -> Prop :=
    | extension_nil : forall m,
      m extends nil

    | extension_cons : forall m m' v v' T,
      m extends m' ->
      (cons (v, T) m) extends (cons (v', T) m') 

    where " m 'extends' m' " := (extension m m').

  Ltac nil_never_extends :=
    match goal with
    F : nil extends (cons _ _) |- _ => inv F
    end.

  Lemma refl : forall m,
    m extends m.
  Proof.
    intros. induction m; eauto using extension.
    match goal with |- (cons ?vT _) extends _ => destruct vT end.
    eauto using extension.
  Qed.

  Lemma trans : forall m m' m'',
    m  extends m'  ->
    m' extends m'' ->
    m  extends m''.
  Proof.
    intros * Hext **. generalize dependent m''.
    induction Hext; intros; destruct m'';
    eauto using extension; try nil_never_extends.
    match goal with H : (cons _ _) extends (cons _ _) |- _ => inv H end.
    eauto using extension.
  Qed.

  Lemma array_add : forall m vT,
    (m +++ vT) extends m.
  Proof.
    intros. induction m; unfold Array.add; eauto using extension. simpl in *.
    match goal with |- (cons ?vT _) extends _ => destruct vT end.
    eauto using extension.
  Qed.

  Lemma array_get : forall m m' ad,
    ad < #m' ->
    m extends m' ->
    m[ad].typ = m'[ad].typ.
  Proof.
    intros * Hlen Hext. generalize dependent ad. generalize dependent m.
    induction m'; intros; try solve [inv Hlen].
    destruct m; try nil_never_extends. invc Hext.
    destruct ad; simpl; trivial. eauto using Arith.Lt.lt_S_n.
  Qed.

  Lemma array_set : forall m ad v T,
    m[ad].typ = T -> 
    m[ad <- (v, T)] extends m.
  Proof.
    intros. generalize dependent ad.
    induction m; intros; eauto using extension. destruct ad;
    match goal with |- _ extends (cons ?vT _) => destruct vT; subst end;
    eauto using refl, extension.
  Qed.

  Lemma memext_mstep : forall m m' t t' e,
    consistently_typed_references m t ->
    m / t ==[e]==> m' / t' ->
    m' extends m.
  Proof.
    intros. invc_mstep; eauto using refl, array_add.
    eapply array_set. induction_tstep; intros; inv_ctr; eauto.
    inv_ctr; trivial.
  Qed.

  Theorem memext_cstep : forall m m' ths ths' tid e,
    forall_threads ths (consistently_typed_references m) ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    m' extends m.
  Proof.
    intros. inv_cstep; eauto using refl, memext_mstep.
  Qed.
End MemExt.

Theorem memtyp_cstep_preservation : forall m m' ths ths' tid e ad,
  forall_threads ths (consistently_typed_references m) ->
  (* --- *)
  ad < #m ->
  m / ths ~~[tid, e]~~> m' / ths' ->
  m[ad].typ = m'[ad].typ.
Proof.
  symmetry. eauto using MemExt.array_get, MemExt.memext_cstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* memtyp inconsistency                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma memtyp_inconsistency : forall m1 m2 t1 t2 ad,
  forall_memory m1 value ->
  forall_memory m2 value ->
  forall_memory m1 (consistently_typed_references m1) ->
  forall_memory m2 (consistently_typed_references m2) ->
  consistently_typed_references m1 t1 ->
  consistently_typed_references m2 t2 ->
  (* --- *)
  safe_access ad m1 t1 ->
  unsafe_access ad m2 t2 ->
  m1[ad].typ <> m2[ad].typ.
Proof.
  intros * ? ? ? ? ? Heq Hsacc Huacc.
  eapply memtyp_immut_iff_sacc in Hsacc as [? Htyp1]; eauto using sacc_then_acc.
  eapply memtyp_mut_iff_uacc   in Huacc as [? Htyp2]; eauto using uacc_then_acc.
  rewrite Htyp1. rewrite Htyp2. discriminate.
Qed.

