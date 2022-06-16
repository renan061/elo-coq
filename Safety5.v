From Coq Require Import Arith.Arith.
From Coq Require Import List.

From Elo Require Import Array.
From Elo Require Import Core0.
From Elo Require Import Safety.















Import ListNotations.

Definition access_map m t (ads : list addr) :=
  forall ad, access m t ad <-> In ad ads.

(* Terms *)

Lemma access_map_tm_nil : forall m,
  access_map m TM_Nil [].
Proof.
  intros. split; intros F; inversion F.
Qed.

Lemma access_map_tm_num : forall m n,
  access_map m (TM_Num n) [].
Proof.
  intros. split; intros F; inversion F.
Qed.

Lemma access_map_tm_loc : forall m ad ads,
  access_map m (get TM_Nil m ad) ads ->
  access_map m (TM_Loc ad) (ad :: ads).
Proof.
  intros * H ad'. specialize (H ad') as [? ?]. split; 
  destruct (Nat.eq_dec ad ad'); subst; eauto using in_eq, access;
  intros H'; inversion H'; subst; eauto using access, in_eq, in_cons.
Qed.

Lemma access_map_tm_new : forall m t ads,
  access_map m t ads <-> access_map m (TM_New t) ads.
Proof.
  intros. split; intros H ad; specialize (H ad) as [? ?];
  split; eauto using access, new_access.
Qed.

Lemma access_map_tm_load : forall m t ads,
  access_map m t ads <-> access_map m (TM_Load t) ads.
Proof.
  intros. split; intros H ad; specialize (H ad) as [? ?];
  split; eauto using access, load_access.
Qed.

Lemma access_map_tm_asg : forall m l r adsL adsR,
  access_map m l adsL ->
  access_map m r adsR ->
  access_map m (TM_Asg l r) (adsL ++ adsR).
Proof.
  intros * Hl Hr ad.
  specialize (Hl ad) as [? ?].
  specialize (Hr ad) as [? ?].
  split; intros H'.
  - eapply asg_access in H' as [? | ?]; eauto using in_or_app.
  - eapply in_app_or in H' as [? | ?]; eauto using access.
Qed.

Lemma access_map_tm_seq : forall m t1 t2 ads1 ads2,
  access_map m t1 ads1 ->
  access_map m t2 ads2 ->
  access_map m (TM_Seq t1 t2) (ads1 ++ ads2).
Proof.
  intros * H1 H2 ad.
  specialize (H1 ad) as [? ?].
  specialize (H2 ad) as [? ?].
  split; intros H'.
  - eapply seq_access in H' as [? | ?]; eauto using in_or_app.
  - eapply in_app_or in H' as [? | ?]; eauto using access.
Qed.

(* Effects *)

Lemma access_map_eff_none : forall m m' t t' ads ads',
  access_map m t ads ->
  m / t ==[EF_None]==> m' / t' ->
  access_map m' t' ads' ->
  (forall ad, In ad ads' -> In ad ads).
Proof.
  assert (forall m t t' ad,
    access m t' ad ->
    t --[EF_None]--> t' ->
    access m t ad). {
      intros * Hacc Hstep.
      remember EF_None as eff; induction Hstep; inversion Heqeff; subst;
      eauto using access, load_access;
      try (eapply asg_access in Hacc || eapply seq_access in Hacc);
      specialize Hacc as [? | ?]; eauto using access.
  }
  intros * Hmap Hmstep Hmap'.
  inversion Hmstep as [? ? ? Hstep | | |]; subst; clear Hmstep.
  intros ? H'. eapply Hmap' in H'. eapply Hmap. eauto.
Qed.

Lemma access_map_eff_load : forall m m' t t' ad v ads ads',
  access_map m t ads ->
  m / t ==[EF_Load ad v]==> m' / t' ->
  access_map m' t' ads' ->
  (forall ad', In ad' ads' -> In ad' ads).
Proof.
  assert (forall m t t' ad ad',
    access m t' ad ->
    t --[EF_Load ad' (get TM_Nil m ad')]--> t' ->
    access m t ad). {
      intros * Hacc Hstep.
      remember (EF_Load ad' (get TM_Nil m ad')) as eff;
      induction Hstep; inversion Heqeff; subst;
      eauto using access, load_access;
      try (eapply asg_access in Hacc || eapply seq_access in Hacc);
      specialize Hacc as [? | ?]; eauto using access.
  }
  intros * Hmap Hmstep Hmap'.
  inversion Hmstep as [| | ? ? ? ? Hstep |]; subst; clear Hmstep.
  intros ? H'. eapply Hmap' in H'. eapply Hmap. eauto.
Qed.

(*
  TM_New
  TM_Load
  TM_Asg
  TM_Seq
  TM_Spawn
*)
(*
  well_behaved_map m t map ->
  m / t ==[eff]==> m' / t' ->
  well_behaved_map m' t' map' ->

  Se (eff = EF_None)  então (map' <= map)
  Se (eff = EF_Alloc) então (map' >  map) -> (map' = (length m) :: map)
  Se (eff = EF_Load)  então (map' <= map) -> (map' = map) \/ (map' = ad :: map)
  Se (eff = EF_Store) então (map' <= map) -> (map' = map) \/ (map' = ad :: map)

*)

