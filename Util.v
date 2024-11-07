From Coq Require Logic.ClassicalFacts.
From Coq Require Import Logic.Decidable.
From Coq Require Import Lia.

Ltac gendep x := generalize dependent x.

(* inversion shortcuts *)

Ltac inv H := inversion H; subst.

Ltac invc H := inv H; clear H.

(* miscellaneous utilities *)

Ltac duplicate H H' := specialize H as H'.
Ltac dup H H' := duplicate H H'.

Ltac auto_specialize := (* TODO: deprecated *)
  match goal with
  | P : ?x, H : ?x -> _ |- _ => specialize (H P)
  | H : ?x = ?x -> _ |- _ => specialize (H eq_refl) 
  end.

Ltac aspecialize := auto_specialize.

Ltac clean :=
  match goal with
  | H1 : ?H, H2 : ?H |- _ => clear H1
  | H  : ?a = ?a     |- _ => clear H
  end.

Ltac invc_eq := 
  match goal with
  | H1 : ?x = ?a, H2 : ?x = ?b |- _ => rewrite H1 in H2; invc H2
  | H  : Some ?x = Some ?y     |- _ => invc H
  end.

#[export] Hint Extern 4 =>
  match goal with
  | _ : False        |- _ => contradiction
  | F : ?x <> ?x     |- _ => contradict F; eauto
  | _ : ?x, _ : ~ ?x |- _ => contradiction
  | F : false = true |- _ => inv F
  | F : true = false |- _ => inv F
  | _ : ?n < ?n      |- _ => lia
  | _ : ?n > ?n      |- _ => lia
  | _ : ?n > ?n      |- _ => lia
  | _ : ?m < ?n      |- _ => assert (m <> n) by lia
  | H1 : ?x = ?a
  , H2 : ?x = ?b     |- _ => try solve [rewrite H1 in H2; discriminate]
  end : core.

Axiom excluded_middle : ClassicalFacts.excluded_middle.

Corollary classic_decidable : forall (P : Prop),
  decidable P.
Proof.
  intros. unfold decidable. eauto using excluded_middle.
Qed.

(* dec *)

From Coq Require Arith.Compare_dec.
From Coq Require Arith.Peano_dec.
From Coq Require Strings.String.

Definition bool_eq_dec  := Bool.bool_dec.
Definition nat_eq_dec   := Peano_dec.eq_nat_dec.
Definition str_eq_dec   := String.string_dec.
Definition lt_eq_lt_dec := Compare_dec.lt_eq_lt_dec.

Lemma opt_dec : forall {A} (o : option A),
  {o = None} + {exists a, o = Some a}.
Proof.
  destruct o; eauto.
Qed.

Lemma alt_opt_dec : forall {A} (o : option A),
  {o = None} + {o <> None}.
Proof.
  intros. destruct o; eauto. right. intros F. invc F.
Qed.

(* misc *)

Lemma ge_iff_le : forall m n,
  m >= n <-> n <= m.
Proof.
  intros; split; destruct n; eauto.
Qed.

