From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Elo Require Import Map.
From Elo Require Import Properties.
From Elo Require Import Lemmas.
From Elo Require Import Preservation.
From Elo Require Import PtrTyp.
From Elo Require Import Soundness.
From Elo Require Import Multistep.

Inductive has_address (ad : addr) : tm  -> Prop :=
  | ha_ref : forall T,
    has_address ad <{&ad :: T}>

  | ha_new : forall T t,
    has_address ad t ->
    has_address ad <{new T t}>

  | ha_load : forall t,
    has_address ad t ->
    has_address ad <{*t}>

  | ha_asg1 : forall t1 t2,
    has_address ad t1 ->
    has_address ad <{t1 = t2}>

  | ha_asg2 : forall t1 t2,
    has_address ad t2 ->
    has_address ad <{t1 = t2}>

  | ha_fun : forall x T t,
    has_address ad t ->
    has_address ad <{fn x T t}>

  | ha_call1 : forall t1 t2,
    has_address ad t1 ->
    has_address ad <{call t1 t2}>

  | ha_call2 : forall t1 t2,
    has_address ad t2 ->
    has_address ad <{call t1 t2}>

  | ha_seq1 : forall t1 t2,
    has_address ad t1 ->
    has_address ad <{t1; t2}>

  | ha_seq2 : forall t1 t2,
    has_address ad t2 ->
    has_address ad <{t1; t2}>
  .

Lemma ha_dec : forall ad t,
  Decidable.decidable (has_address ad t).
Proof.
  unfold Decidable.decidable. intros. induction t;
  try solve
    [ right; intros F; inv F
    | try (destruct IHt || destruct IHt1, IHt2) ; solve
        [ left; eauto using has_address
        | right; intros F; inv F; contradiction
        ]
    ].
  destruct (nat_eq_dec ad n); subst; eauto using has_address.
  right. intros F. inv F. contradiction.
Qed.

Lemma ha_then_acc : forall ad m t,
  has_address ad t -> access ad m t.
Proof.
  intros * Hha. induction Hha; eauto using access.
Qed.

Lemma acc'_dec : forall ad m t,
  Decidable.decidable (access ad m t).
Proof.
  unfold Decidable.decidable. intros.
  assert (Decidable.decidable (has_address ad t)) as [? | ?]
    by eauto using ha_dec;
  eauto using ha_then_acc.
  (* has_address ad' t /\ access ad m m[ad'] *)
Abort.
