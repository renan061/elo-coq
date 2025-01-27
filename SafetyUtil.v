From Coq Require Import Lists.List.

From Elo Require Import Core.
From Elo Require Import SyntacticProperties.
From Elo Require Import TypeProperties.

From Elo Require Import Invariants.

(* ------------------------------------------------------------------------- *)
(* in-app-head & in-app-tail                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma in_app_head : forall {A} (l : list A) (a : A),
  In a (l ++ a :: nil).
Proof.
  intros. induction l; simpl; eauto.
Qed.

Lemma in_app_tail : forall {A} (l : list A) (a a' : A),
  In a l ->
  In a (l ++ a' :: nil).
Proof.
  intros. induction l; simpl in *; auto.
  match goal with H : _ \/ _ |- _ => destruct H end; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* destruct-ustep                                                            *)
(* ------------------------------------------------------------------------- *)

Local Lemma _destruct_ustep1 : forall tc m1 m2 ths1 ths2 tid e,
  m1 \ ths1 ~~[tc +++ (tid, e)]~~>* m2 \ ths2 ->
  (exists mA thsA,
    m1 \ ths1 ~~[tid, e]~~>  mA \ thsA /\
    mA \ thsA ~~[tc    ]~~>* m2 \ ths2 ).
Proof.
  intros ?. induction tc; intros; invc_ustep.
  - invc_ustep. eauto using multistep.
  - match goal with Hustep : _ \ _ ~~[ _ ]~~>* _ \ _ |- _ => 
      decompose record (IHtc _ _ _ _ _ _ Hustep); eauto using multistep
    end.
Qed.

Ltac destruct_ustep1 :=
  match goal with
  | H : _ \ _  ~~[_ +++ (_, _)]~~>* _ \ _ |- _ =>
    eapply _destruct_ustep1 in H as [mA [thsA [H1A HA2]]]
  end.

(* ------------------------------------------------------------------------- *)

Local Lemma _destruct_ustep2 : forall tc m1 m4 ths1 ths4 tid1 tid2 e1 e2,
  m1 \ ths1 ~~[(tid2, e2) :: tc +++ (tid1, e1)]~~>* m4 \ ths4 ->
  (exists m2 m3 ths2 ths3,
    m1 \ ths1 ~~[tid1, e1]~~>  m2 \ ths2 /\
    m2 \ ths2 ~~[tc      ]~~>* m3 \ ths3 /\
    m3 \ ths3 ~~[tid2, e2]~~>  m4 \ ths4 ).
Proof.
  intros. invc_ustep. destruct_ustep1. do 4 eexists. repeat split; eauto.
Qed.

Ltac destruct_ustep2 :=
  match goal with 
  | H : _ \ _ ~~[(_, _) :: _ +++ (_, _)]~~>* _ \ _ |- _ =>
    eapply _destruct_ustep2 in H as [mA [mB [thsA [thsB [H1A [HAB HB2]]]]]]
  end.

(* ------------------------------------------------------------------------- *)

Local Lemma _destruct_ustep3 : forall m1 m2 ths1 ths2 tc1 tc2 tid e,
  m1 \ ths1 ~~[tc2 ++ (tid, e) :: tc1]~~>* m2 \ ths2 ->
  exists mA mB thsA thsB,
    m1 \ ths1 ~~[tc1   ]~~>* mA \ thsA /\
    mA \ thsA ~~[tid, e]~~>  mB \ thsB /\
    mB \ thsB ~~[tc2   ]~~>* m2 \ ths2.
Proof.
  intros.
  gendep ths2. gendep ths1. gendep m2. gendep m1. gendep e. gendep tid.
  induction tc2; intros.
  - rewrite app_nil_l in *. invc_ustep. repeat eexists; eauto using multistep.
  - invc_ustep.
    match goal with H : _ \ _ ~~[_]~~>* _ \ _ |- _ =>
      decompose record (IHtc2 _ _ _ _ _ _ H)
    end.
    repeat eexists; eauto using multistep.
Qed.

Ltac destruct_ustep3 :=
  match goal with 
  | H : _ \ _ ~~[_ ++ (_, _) :: _]~~>* _ \ _ |- _ =>
    eapply _destruct_ustep3 in H as [mA [mB [thsA [thsB [H1A [HAB HB2]]]]]]
  end.

