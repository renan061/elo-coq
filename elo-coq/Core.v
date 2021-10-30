From Coq Require Init.Nat.

From Elo Require Export Array.
From Elo Require Export Map.

Definition name := String.string.
Definition num := nat.

(* Notations *)

Reserved Notation "'[' id ':=' x ']' t" (at level 20, id constr).
Reserved Notation "D / m / t '-->' D' / m' / t'" (at level 40,
  m at next level, t at next level, D' at next level, m' at next level).
Reserved Notation "Gamma '|--' t 'is' T" (at level 40, t at next level).
Reserved Notation "D / mt / Gamma '|--' t 'is' T" (at level 40,
  mt at next level, Gamma at next level).
Reserved Notation "D / Gamma '|--' t" (at level 40, Gamma at next level).

(* Types *)

Inductive typ : Set :=
  (* primitive types *)
  | TY_Void
  | TY_Num
  (* internal types *)
  | TY_Ref : typ -> typ
  | TY_ImmutRef : typ -> typ
  .

(* Terms *)

Inductive tm : Set :=
  (* expressions *)
  | TM_Nil
  | TM_Num : num -> tm
  | TM_Id : name -> tm
  (* statements *)
  | TM_Asg : tm -> tm -> tm
  | TM_Call : name -> tm -> tm
  | TM_Seq : tm -> tm -> tm
  (* definitions *)
  | TM_LetVal : name -> typ -> tm -> tm -> tm
  | TM_LetVar : name -> typ -> tm -> tm -> tm
  | TM_LetFun : name -> name -> typ -> tm -> typ -> tm -> tm
  (* internal *)
  | TM_Loc : nat -> tm
  | TM_Load : tm -> tm
  .

(* Values *)

Inductive value : tm -> Prop :=
  | V_Nil : value TM_Nil
  | V_Num : forall n, value (TM_Num n)
  (* internal *)
  | V_Loc : forall i, value (TM_Loc i)
  .

(* Auxiliary Aliases *)

Definition defs := map tm.
Definition ctx := map typ.
Definition mem := list tm.
Definition memtyp := list typ.

Definition get_typ := get TY_Void.
Definition get_tm  := get TM_Nil.

(* Operational Semantics *)

Local Infix "=?" := String.eqb (at level 70, no associativity).

(* [id := x] t *)
Fixpoint subst (id : name) (x t : tm) : tm :=
  match t with
  | TM_Nil => t
  | TM_Num _ => t
  | TM_Id id' => if id =? id' then x else t
  | TM_Asg t' e => TM_Asg ([id := x] t') ([id := x] e)
  | TM_Call f e => TM_Call f ([id := x] e)
  | TM_Seq t1 t2 => TM_Seq ([id := x] t1) ([id := x] t2)
  | TM_LetVal id' E e t' => TM_LetVal id' E ([id := x] e)
    (if id =? id' then t' else ([id := x] t'))
  | TM_LetVar id' E e t' => TM_LetVar id' E ([id := x] e)
    (if id =? id' then t' else ([id := x] t'))
  | TM_LetFun f p P block R t' => 
    TM_LetFun f p P
      (if id =? p then block else ([id := x] block)) R
      (if id =? f then t' else ([id := x] t'))
  | TM_Loc _ => t
  | TM_Load t' => TM_Load ([id := x] t')
  end
  where "'[' id ':=' x ']' t" := (subst id x t).

Inductive step : defs -> mem -> tm -> defs -> mem -> tm -> Prop :=
  | ST_Asg1 : forall D m m' t e e',
    D / m / e --> D / m' / e' ->
    D / m / TM_Asg t e --> D / m' / TM_Asg t e'

  | ST_Asg2 : forall D m m' t t' e,
    value e ->
    D / m / t --> D / m' / t' ->
    D / m / TM_Asg t e --> D / m' / TM_Asg t' e

  | ST_Asg : forall D m i e,
    value e ->
    i < length m ->
    D / m / TM_Asg (TM_Loc i) e --> D / (set m i e) / TM_Nil

  | ST_Call1 : forall D m m' id e e',
    D / m / e --> D / m' / e' -> 
    D / m / TM_Call id e --> D / m' / TM_Call id e'

  | ST_Call : forall D m id e f p P block R,
    value e ->
    lookup D id = Some (TM_LetFun f p P block R TM_Nil) ->
    D / m / TM_Call id e --> D / m / [p := e] block
    (* TODO O block avalia com o D local; fica com as definições erradas. *)
    (* Criar um novo tipo indutivo para guardar as coisas das definições *)

  | ST_Seq1 : forall D m m' t1 t2 t,
    D / m / t1 --> D / m' / t2 ->
    D / m / TM_Seq t1 t --> D / m' / TM_Seq t2 t

  | ST_Seq : forall D m t,
    D / m / TM_Seq TM_Nil t --> D / m / t

  | ST_LetVal1 : forall D m m' id E e e' t,
    D / m / e --> D / m' / e' ->
    D / m / TM_LetVal id E e t --> D / m' / TM_LetVal id E e' t

  | ST_LetVal : forall D m id E e t,
    let m' := add m e in
    let i := length m' in
    value e ->
    D / m / TM_LetVal id E e t --> D / m' / [id := TM_Loc i] t

  (* OK *)
  (*
  | ST_LetVal : forall D m id E e t,
    value e ->
    D / m / TM_LetVal id E e t --> D / m' / [id := e] t
  *)

  | ST_LetVar1 : forall D m m' id E e e' t,
    D / m / e --> D / m' / e' ->
    D / m / TM_LetVar id E e t --> D / m' / TM_LetVar id E e' t

  | ST_LetVar : forall D m m' id E e t,
    m' = add m e ->
    value e ->
    D / m / TM_LetVar id E e t --> D / m' / [id := TM_Loc (length m')] t

  | ST_LetFun : forall D D' m f p P b R t,
    D' = update D f (TM_LetFun f p P b R TM_Nil) ->
    D / m / TM_LetFun f p P b R t --> D' / m / t

  | ST_Load1 : forall D D' m m' t t',
    D / m / t --> D' / m' / t' ->
    D / m / TM_Load t --> D' / m' / TM_Load t'

  | ST_Load : forall D m i,
    D / m / TM_Load (TM_Loc i) --> D / m / (get_tm m i)

  where "D / m / t '-->' D' / m' / t'" := (step D m t D' m' t').

(* Typing *)

Inductive typeof {D : defs} {mt : memtyp} : ctx -> tm -> typ -> Prop :=
  | T_Nil : forall Gamma,
    Gamma |-- TM_Nil is TY_Void

  | T_Num : forall Gamma n,
    Gamma |-- (TM_Num n) is TY_Num

  | T_Id_Val : forall Gamma id A,
    lookup Gamma id = Some (TY_ImmutRef A) ->
    Gamma |-- (TM_Id id) is (TY_ImmutRef A)

  | T_Id_Var : forall Gamma id A,
    lookup Gamma id = Some (TY_Ref A) ->
    Gamma |-- (TM_Id id) is (TY_Ref A)

  | T_Asg : forall Gamma t e A,
    Gamma |-- t is (TY_Ref A) ->
    Gamma |-- e is A ->
    Gamma |-- (TM_Asg t e) is TY_Void

  | T_Call : forall Gamma id e f p P block R,
    lookup D id = Some (TM_LetFun f p P block R TM_Nil) ->
    Gamma |-- e is P ->    
    Gamma |-- (TM_Call id e) is R

  | T_Seq : forall Gamma t t' A,
    Gamma |-- t  is TY_Void ->
    Gamma |-- t' is A ->
    Gamma |-- (TM_Seq t t') is A

  | T_LetVal : forall Gamma id e t A B,
    Gamma  |-- e is A ->
    (update Gamma id (TY_ImmutRef A)) |-- t is B ->
    Gamma  |-- (TM_LetVal id A e t) is B

  | T_LetVar : forall Gamma id e t A B,
    Gamma  |-- e is A ->
    (update Gamma id (TY_Ref A)) |-- t is B ->
    Gamma  |-- (TM_LetVar id A e t) is B

  | T_Loc : forall Gamma i,
    i < length mt -> (* TODO *)
    Gamma |-- (TM_Loc i) is TY_Ref (get_typ mt i)

  | T_Load_Ref : forall Gamma t A,
    Gamma |-- t is TY_Ref A ->
    Gamma |-- (TM_Load t) is A

  | T_Load_ImmutRef : forall Gamma t A,
    Gamma |-- t is TY_ImmutRef A ->
    Gamma |-- (TM_Load t) is A

  where "Gamma '|--' t 'is' T" := (typeof Gamma t T)
  and "D / mt / Gamma '|--' t 'is' T" := (@typeof D mt Gamma t T).

Inductive well_typed : defs -> ctx -> tm -> Prop :=
  | T_DefVal : forall D m Gamma Gamma' id e E t T,
    Gamma' = update Gamma id (TY_ImmutRef E) ->
    D / m / Gamma  |-- e is E ->
    D / m / Gamma' |-- t is T ->
    D / Gamma |-- TM_LetVal id E e t

  | T_DefFun : forall D m Gamma f p P b R t,
    D  / m / (update empty p P) |-- b is R ->
    update D f (TM_LetFun f p P b R TM_Nil) / Gamma |-- t ->
    D  / Gamma |-- TM_LetFun f p P b R t

  where "D / Gamma '|--' t" := (well_typed D Gamma t).

(* Proofs *)

Lemma value_does_not_step : forall D D' m m' v t,
  value v -> ~ (D / m / v --> D' / m' / t).
Proof.
  intros * Hv Hstep. destruct Hv; inversion Hstep.
Qed.

Theorem deterministic_step : forall D D' m m' t t1 t2,
  D / m / t --> D' / m' / t1 ->
  D / m / t --> D' / m' / t2 ->
  t1 = t2.
Proof.
  intros * Hstep1.
  generalize dependent t2.
  induction Hstep1;
  intros * Hstep2;
  inversion Hstep2; subst;
  solve
    [ exfalso; eapply value_does_not_step; eauto
    | reflexivity 
    | inversion Hstep1
    | congruence
    | match goal with
      | F : _ / _ / TM_Loc _ --> _ / _ / _ |- _ => inversion F
      | F : _ / _ / TM_Nil   --> _ / _ / _ |- _ => inversion F
      | H : forall x, _ / _ / _ --> _ / _ / x -> _ = x |- _ => erewrite H; eauto
      end
    ].
Qed.

Theorem deterministic_typing : forall D mt Gamma t X Y,
  D / mt / Gamma |-- t is X ->
  D / mt / Gamma |-- t is Y ->
  X = Y.
Proof.
  assert (forall A B, TY_Ref A = TY_Ref B -> A = B). congruence.
  assert (forall A B, TY_ImmutRef A = TY_ImmutRef B -> A = B). congruence.
  assert (iref_neq_ref : forall A B, TY_ImmutRef A <> TY_Ref B). congruence.
  assert (ref_neq_iref : forall A B, TY_Ref A <> TY_ImmutRef B). congruence.

  intros * HX.
  generalize dependent Y.
  induction HX; intros Y HY;
  inversion HY; subst; try solve [congruence | auto];
  match goal with H : context [?C _ = _] |- _ = _ =>
    exfalso;
    match C with
    | TY_Ref => eapply ref_neq_iref
    | TY_ImmutRef => eapply iref_neq_ref
    end;
    eauto
  end.
Qed.
