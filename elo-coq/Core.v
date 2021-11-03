From Coq Require Init.Nat.

From Elo Require Export Array.
From Elo Require Export Map.

Definition name := String.string.
Definition num := nat.

(* Notations *)

Reserved Notation "'[' id ':=' x ']' t" (at level 20, id constr).
Reserved Notation "m / t '-->' m' / t'" (at level 40,
  t at next level, m' at next level).
Reserved Notation "Gamma '|--' t 'is' T" (at level 40, t at next level).
Reserved Notation "mt / Gamma '|--' t 'is' T" (at level 40,
  Gamma at next level).
Reserved Notation "Gamma '|--' t" (at level 40).

(* Types *)

Inductive typ : Set :=
  (* primitive types *)
  | TY_Void
  | TY_Num
  (* internal types *)
  | TY_Ref : typ -> typ
  | TY_ImmutRef : typ -> typ
  | TY_Fun : typ -> typ -> typ
  .

(* Terms *)

Inductive tm : Set :=
  (* expressions *)
  | TM_Nil
  | TM_Num : num -> tm
  | TM_Id : name -> tm
  (* statements *)
  | TM_Asg : tm -> tm -> tm
  | TM_Call : tm -> tm -> tm
  | TM_Seq : tm -> tm -> tm
  (* definitions *)
  | TM_LetVal : name -> typ -> tm -> tm -> tm
  | TM_LetVar : name -> typ -> tm -> tm -> tm
  | TM_LetFun : name -> typ -> tm -> tm -> tm
  (* internal terms *)
  | TM_Loc : nat -> tm
  | TM_Load : tm -> tm
  | TM_Fun : name -> typ -> tm -> typ -> tm
  .

(* Values *)

Inductive value : tm -> Prop :=
  | V_Nil : value TM_Nil
  | V_Num : forall n, value (TM_Num n)
  (* internal *)
  | V_Loc : forall i, value (TM_Loc i)
  | V_Fun : forall p P block R, value (TM_Fun p P block R)
  .

(* Auxiliary Aliases *)

Definition ctx := map typ.
Definition mem := list tm.
Definition mem_typ := list typ.

Definition get_typ := get TY_Void.
Definition get_tm  := get TM_Nil.

(* Operational Semantics *)

Local Infix "=?" := String.eqb (at level 70, no associativity).

Fixpoint subst (id : name) (x t : tm) : tm :=
  match t with
  | TM_Nil => t
  | TM_Num _ => t
  | TM_Id id' => if id =? id' then x else t
  | TM_Asg t' e => TM_Asg ([id := x] t') ([id := x] e)
  | TM_Call f a => TM_Call ([id := x] f) ([id := x] a)
  | TM_Seq t1 t2 => TM_Seq ([id := x] t1) ([id := x] t2)
  | TM_LetVal id' E e t' => TM_LetVal id' E ([id := x] e)
    (if id =? id' then t' else ([id := x] t'))
  | TM_LetVar id' E e t' => TM_LetVar id' E ([id := x] e)
    (if id =? id' then t' else ([id := x] t'))
  | TM_LetFun id' F f t' => TM_LetFun id' F ([id := x] f)
    (if id =? id' then t' else [id := x] t')
  | TM_Loc _ => t
  | TM_Load t' => TM_Load ([id := x] t')
  | TM_Fun p P block R => if id =? p then t else TM_Fun p P ([id := x] block) R
  end
  where "'[' id ':=' x ']' t" := (subst id x t).

Inductive step : mem -> tm -> mem -> tm -> Prop :=
  | ST_Asg1 : forall m m' t e e',
    m / e --> m' / e' ->
    m / TM_Asg t e --> m' / TM_Asg t e'

  | ST_Asg2 : forall m m' t t' e,
    value e ->
    m / t --> m' / t' ->
    m / TM_Asg t e --> m' / TM_Asg t' e

  | ST_Asg : forall m i e,
    value e ->
    i < length m ->
    m / TM_Asg (TM_Loc i) e --> (set m i e) / TM_Nil

  | ST_Call1 : forall m m' f a a',
    m / a --> m' / a' ->
    m / TM_Call f a --> m' / TM_Call f a'

  | ST_Call2 : forall m m' f f' a,
    value a ->
    m / f --> m' / f' ->
    m / TM_Call f a --> m' / TM_Call f' a

  | ST_Call : forall m a p P block R,
    value a ->
    m / TM_Call (TM_Fun p P block R) a --> m / [p := a] block

  | ST_Seq1 : forall m m' t1 t2 t,
    m / t1 --> m' / t2 ->
    m / TM_Seq t1 t --> m' / TM_Seq t2 t

  | ST_Seq : forall m t,
    m / TM_Seq TM_Nil t --> m / t

  | ST_LetVal1 : forall m m' id E e e' t,
    m / e --> m' / e' ->
    m / TM_LetVal id E e t --> m' / TM_LetVal id E e' t

  | ST_LetVal : forall m id E e t,
    value e ->
    m / TM_LetVal id E e t --> m / [id := e] t

  | ST_LetVar1 : forall m m' id E e e' t,
    m / e --> m' / e' ->
    m / TM_LetVar id E e t --> m' / TM_LetVar id E e' t

  | ST_LetVar : forall m id E e t,
    value e ->
    m / TM_LetVar id E e t --> (add m e) / [id := TM_Loc (length m)] t

  | ST_LetFun1 : forall m m' id F f f' t,
    m / f --> m' / f' ->
    m / TM_LetFun id F f t --> m' / TM_LetFun id F f' t

  | ST_LetFun : forall m id F f t,
    value f ->
    m / TM_LetFun id F f t --> m / [id := f] t

  | ST_Load1 : forall m m' t t',
    m / t --> m' / t' ->
    m / TM_Load t --> m' / TM_Load t'

  | ST_Load : forall m i,
    m / TM_Load (TM_Loc i) --> m / (get_tm m i)

  where "m / t '-->' m' / t'" := (step m t m' t').

(* Typing *)

Inductive typeof {mt : mem_typ} : ctx -> tm -> typ -> Prop :=
  | T_Nil : forall Gamma,
    Gamma |-- TM_Nil is TY_Void

  | T_Num : forall Gamma n,
    Gamma |-- (TM_Num n) is TY_Num

  | T_Id_Val : forall Gamma id T,
    lookup Gamma id = Some (TY_ImmutRef T) ->
    Gamma |-- (TM_Id id) is (TY_ImmutRef T)

  | T_Id_Var : forall Gamma id T,
    lookup Gamma id = Some (TY_Ref T) ->
    Gamma |-- (TM_Id id) is (TY_Ref T)

  | T_Asg : forall Gamma t e T,
    Gamma |-- t is (TY_Ref T) ->
    Gamma |-- e is T ->
    Gamma |-- (TM_Asg t e) is TY_Void

  | T_Call : forall Gamma f a P R,
    Gamma |-- f is (TY_Fun P R) ->
    Gamma |-- a is P ->
    Gamma |-- (TM_Call f a) is R

  | T_Seq : forall Gamma t t' T,
    Gamma |-- t  is TY_Void ->
    Gamma |-- t' is T ->
    Gamma |-- (TM_Seq t t') is T

  | T_LetVal : forall Gamma id e t E T,
    Gamma |-- e is E ->
    (update Gamma id E) |-- t is T ->
    Gamma |-- (TM_LetVal id E e t) is T

  | T_LetVar : forall Gamma id e t E T,
    Gamma  |-- e is E ->
    (update Gamma id (TY_Ref E)) |-- t is T ->
    Gamma  |-- (TM_LetVar id E e t) is T

  | T_LetFun : forall Gamma id F P R f t T,
    F = TY_Fun P R ->
    Gamma |-- f is F ->
    (update Gamma id F) |-- t is T ->
    Gamma |-- (TM_LetFun id F f t) is T

  | T_Loc : forall Gamma i,
    i < length mt ->
    Gamma |-- (TM_Loc i) is TY_Ref (get_typ mt i)

  | T_Load_Ref : forall Gamma t T,
    Gamma |-- t is TY_Ref T ->
    Gamma |-- (TM_Load t) is T

  | T_Load_ImmutRef : forall Gamma t T,
    Gamma |-- t is TY_ImmutRef T ->
    Gamma |-- (TM_Load t) is T

  | T_Fun : forall Gamma p P block R,
    (update Gamma p P) |-- block is R ->
    Gamma |-- (TM_Fun p P block R) is (TY_Fun P R)

  where "Gamma '|--' t 'is' T" := (typeof Gamma t T)
  and "mt / Gamma '|--' t 'is' T" := (@typeof mt Gamma t T).

(* Proofs *)

Lemma value_does_not_step : forall m m' v t,
  value v -> ~ (m / v --> m' / t).
Proof.
  intros * Hv Hstep. destruct Hv; inversion Hstep.
Qed.

Theorem deterministic_step : forall m m' t t1 t2,
  m / t --> m' / t1 ->
  m / t --> m' / t2 ->
  t1 = t2.
Proof.
  intros * Hstep1.
  generalize dependent t2.
  induction Hstep1;
  intros * Hstep2;
  inversion Hstep2; subst;
  try solve
    [ exfalso; eapply value_does_not_step; eauto
    | congruence
    | match goal with
      | F : _ / TM_Loc _ --> _ / _ |- _ => inversion F
      | F : _ / TM_Nil   --> _ / _ |- _ => inversion F
      | H : forall x, _ / _ --> _ / x -> _ = x |- _ => erewrite H; eauto
      end
    ].
  - exfalso; eapply (value_does_not_step _ _ (TM_Fun p P block R));
    eauto using value.
  - exfalso; eapply (value_does_not_step _ _ (TM_Fun p P block R));
    eauto using value.
Qed.

Theorem deterministic_typing : forall mt Gamma t X Y,
  mt / Gamma |-- t is X ->
  mt / Gamma |-- t is Y ->
  X = Y.
Proof.
  assert (forall A B, TY_Ref A = TY_Ref B -> A = B). congruence.
  assert (forall A B, TY_ImmutRef A = TY_ImmutRef B -> A = B). congruence.
  assert (iref_neq_ref : forall A B, TY_ImmutRef A <> TY_Ref B). congruence.
  assert (ref_neq_iref : forall A B, TY_Ref A <> TY_ImmutRef B). congruence.

  intros * HX.
  generalize dependent Y.
  induction HX; intros Y HY;
  inversion HY; subst;
  try solve [congruence | auto];
  try (match goal with H : context [?C _ = _] |- _ = _ =>
    exfalso;
    match C with
    | TY_Ref => eapply ref_neq_iref
    | TY_ImmutRef => eapply iref_neq_ref
    end;
    eauto
  end; fail).
  - apply IHHX1 in H4. apply IHHX2 in H6. congruence.
Qed.
