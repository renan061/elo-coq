From Coq Require Init.Nat.

From Elo Require Export Array.
From Elo Require Export Map.

Definition name := String.string.
Definition num := nat.

(* Notations *)

Reserved Notation "'[' id ':=' x ']' t" (at level 20, id constr).
Reserved Notation "D / m / t '-->' D' / m' / t'" (at level 40,
  m at next level, t at next level, D' at next level, m' at next level).
Reserved Notation "Context '|-' t 'is' T" (at level 40,
  t at next level).
Reserved Notation "D / mt / Context '|-' t 'is' T" (at level 40,
  mt at next level, Context at next level).
Reserved Notation "D / Delta '|-' t" (at level 40,
  Delta at next level).

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
  .

(* Values *)

Inductive value : tm -> Prop :=
  | V_Nil : value TM_Nil
  | V_Num : forall n, value (TM_Num n)
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

(* TODO : shadowing *)
Fixpoint subst (id : name) (x t : tm) : tm :=
  match t with
  | TM_Nil => t
  | TM_Num _ => t
  | TM_Id id' => if String.eqb id id' then x else t
  | TM_Asg t' e => TM_Asg ([id := x] t') ([id := x] e)
  | TM_Call f e => TM_Call f ([id := x] e)
  | TM_Seq t1 t2 => TM_Seq ([id := x] t1) ([id := x] t2)
  | TM_LetVal id' E e t' => if String.eqb id id' then t
    else TM_LetVal id' E ([id := x] e) ([id := x] t')  
  | TM_LetVar id' E e t' => if String.eqb id id' then t
    else TM_LetVar id' E ([id := x] e) ([id := x] t')
  | TM_LetFun f p P b R t' =>  if String.eqb id p then t
    else TM_LetFun f p P ([id := x] b) R ([id := x] t')
  | TM_Loc _ => t
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

  where "D / m / t '-->' D' / m' / t'" := (step D m t D' m' t').

(* Typing *)

Inductive typeof {D : defs} {mt : memtyp} : (ctx * ctx) -> tm -> typ -> Prop :=
  | T_Nil : forall Delta Gamma,
    (Delta, Gamma) |- TM_Nil is TY_Void

  | T_Num : forall Delta Gamma n,
    (Delta, Gamma) |- (TM_Num n) is TY_Num

  | T_IdSharedVal : forall Delta Gamma id A,
    lookup Delta id = Some (TY_ImmutRef A) ->
    lookup Gamma id = None ->
    (Delta, Gamma) |- (TM_Id id) is A

  | T_IdLocalVal : forall Delta Gamma id A,
    lookup Delta id = None ->
    lookup Gamma id = Some (TY_ImmutRef A) ->
    (Delta, Gamma) |- (TM_Id id) is A

  | T_IdVar : forall Delta Gamma id A,
    lookup Delta id = None ->
    lookup Gamma id = Some (TY_Ref A) ->
    (Delta, Gamma) |- (TM_Id id) is A

  | T_Asg : forall Delta Gamma t e A,
    (Delta, Gamma) |- t is (TY_Ref A) ->
    (Delta, Gamma) |- e is A ->
    (Delta, Gamma) |- (TM_Asg t e) is TY_Void

  | T_Call : forall Delta Gamma id e f p P block R,
    lookup D id = Some (TM_LetFun f p P block R TM_Nil) ->
    (Delta, Gamma) |- e is P ->
    (Delta, update Gamma p P) |- block is R -> (* TODO *)
    (Delta, Gamma) |- (TM_Call id e) is R

  | T_Seq : forall Delta Gamma t t' A,
    (Delta, Gamma) |- t is TY_Void ->
    (Delta, Gamma) |- t' is A ->
    (Delta, Gamma) |- (TM_Seq t t') is A

  | T_LetVal : forall Delta Gamma id e t A B,
    (Delta, Gamma)  |- e is A ->
    (Delta, update Gamma id (TY_ImmutRef A)) |- t is B ->
    (Delta, Gamma)  |- (TM_LetVal id A e t) is B

  | T_LetVar : forall Delta Gamma Gamma' id e t A B,
    Gamma' = update Gamma id (TY_Ref A) ->
    (Delta, Gamma)  |- e is A ->
    (Delta, Gamma') |- t is B ->
    (Delta, Gamma)  |- (TM_LetVar id A e t) is B

  | T_Loc : forall Delta Gamma i,
    i < length mt ->
    (Delta, Gamma) |- (TM_Loc i) is TY_Ref (get_typ mt i)

  where "Context '|-' t 'is' T" := (typeof Context t T)
  and "D / mt / Context '|-' t 'is' T" := (@typeof D mt Context t T).

Inductive well_typed : defs -> ctx -> tm -> Prop :=
  | T_DefVal : forall D m Delta Delta' id e E t T,
    Delta' = update Delta id (TY_ImmutRef E) ->
    D / m / (Delta, empty)  |- e is E ->
    D / m / (Delta', empty) |- t is T ->
    D / Delta |- TM_LetVal id E e t

  | T_DefFun : forall D m Delta f p P b R t,
    D  / m / (Delta, update empty p P) |- b is R ->
    update D f (TM_LetFun f p P b R TM_Nil) / Delta |- t ->
    D  / Delta |- TM_LetFun f p P b R t

  where "D / Delta '|-' t" := (well_typed D Delta t).

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
  try solve
    [ exfalso; eapply value_does_not_step; eauto
    | reflexivity 
    | inversion Hstep1
    | match goal with [H : context F [_ = _] |- _] => erewrite H; auto end
    | congruence
    ].
  - inversion H9. (* TODO *)
  - inversion H6. (* TODO *)
Qed.

Theorem deterministic_typing : forall D mt Delta Gamma t X Y,
  D / mt / (Delta, Gamma) |- t is X ->
  D / mt / (Delta, Gamma) |- t is Y ->
  X = Y.
Proof.
  intros * HX HY.
  induction HX; inversion HY; subst; try auto; try congruence.
Qed.
