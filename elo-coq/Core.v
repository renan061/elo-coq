From Coq Require Import Init.Nat.
From Coq Require Import List.

From Elo Require Export Array.
From Elo Require Export Map.

Import ListNotations.

Definition name := String.string.
Definition num := nat.

(* Notations *)

Reserved Notation "'[' id ':=' x ']' t"
  (at level 20, id constr).
Reserved Notation "t '-->' t' # eff"
  (at level 40).
Reserved Notation "t '-->*' t'"
  (at level 40).
Reserved Notation "t '-->+' t'"
  (at level 40).
Reserved Notation "m / threads '==>' m' / threads'"
  (at level 40, threads at next level, m' at next level).
Reserved Notation "m / threads '==>*' m' / threads'"
  (at level 40, threads at next level, m' at next level).
Reserved Notation "Gamma '|--' t 'is' T"
  (at level 40, t at next level).
Reserved Notation "mt / Gamma '|--' t 'is' T"
  (at level 40, Gamma at next level).

(* Types *)

Inductive typ : Set :=
  (* primitive types *)
  | TY_Void
  | TY_Num
  | TY_Arr : typ -> typ
  | TY_IArr : typ -> typ
  (* | TY_TQueue : typ *)
  (* internal types *)
  | TY_Ref : typ -> typ
  | TY_IRef : typ -> typ
  | TY_Fun : typ -> typ -> typ
  .

(*
  | TY_Mon : name -> monitor_type -> typ
with monitor_type : Set :=
  | MonitorTypeNil : monitor_type
  | MonitorTypeCons : name -> typ -> monitor_type -> monitor_type
  .
*)

(* Type Safety *)

Inductive safe_type : typ -> Prop :=
  | SF_Void : safe_type TY_Void
  | SF_Num  : safe_type TY_Num
  | SF_IArr : forall T, safe_type T -> safe_type (TY_IArr T)
  | SF_IRef : forall T, safe_type T -> safe_type (TY_IRef T)
  | SF_Fun  : forall P R, safe_type (TY_Fun P R)
  .

Fixpoint is_safe_type T :=
  match T with
  | TY_Void
  | TY_Num
  | TY_Fun _ _ => true
  | TY_IArr T'
  | TY_IRef T' => is_safe_type T'
  | _ => false
  end.

Lemma safe_type_equivalence : forall T,
  safe_type T <-> is_safe_type T = true.
Proof.
  intros T. split; induction T; intros H;
  try inversion H; auto using is_safe_type, safe_type.
Qed.

Definition safe_context Gamma :=
  forall id T, lookup Gamma id = Some T -> safe_type T.

Definition safe (Gamma : map typ) :=
  fun k => 
    match Gamma k with
    | None => None
    | Some T => if is_safe_type T then Some T else None
    end.

Theorem safe_guarantees_safe_context : forall Gamma,
  safe_context (safe Gamma).
Proof.
  unfold safe_context, lookup, safe. intros Gamma id T.
  destruct (Gamma id); intros H; try discriminate.
  destruct is_safe_type eqn:E; inversion H.
  subst. apply safe_type_equivalence. assumption.
Qed.

Theorem safe_semantics : forall Gamma id T,
  lookup Gamma id = Some T ->
  (   safe_type T  -> lookup (safe Gamma) id = Some T) /\
  (~ (safe_type T) -> lookup (safe Gamma) id = None).
Proof.
  unfold lookup, safe. intros * H1. split;
  intros H2; destruct (Gamma id); inversion H1; subst;
  rewrite safe_type_equivalence in H2;
  try (apply Bool.not_true_is_false in H2);
  rewrite H2; reflexivity.
Qed.

(* Terms *)

Inductive tm : Set :=
  (* expressions *)
  | TM_Nil
  | TM_Num : num -> tm
  | TM_Arr : typ -> num -> tm
  | TM_ArrNew : typ -> tm -> tm
  | TM_ArrIdx : tm -> tm -> tm
  | TM_Id : name -> tm
  (* statements *)
  | TM_Asg : tm -> tm -> tm
  | TM_ArrAsg : tm -> tm -> tm -> tm
  | TM_Call : tm -> tm -> tm
  | TM_Seq : tm -> tm -> tm
  (* concurrency statements *)
  | TM_Spawn : tm -> tm
  (* definitions *)
  | TM_LetVal : name -> typ -> tm -> tm -> tm
  | TM_LetVar : name -> typ -> tm -> tm -> tm
  | TM_LetFun : name -> typ -> tm -> tm -> tm
  (* internal terms *)
  | TM_Loc : num -> tm
  | TM_Load : tm -> tm
  | TM_Fun : name -> typ -> tm -> typ -> tm
  .

(* Values *)

Inductive value : tm -> Prop :=
  | V_Nil    : value TM_Nil
  | V_Num    : forall n, value (TM_Num n)
  | V_Arr    : forall T i, value (TM_Arr T i)
  (* internal *)
  | V_Loc : forall i, value (TM_Loc i)
  | V_Fun : forall p P block R, value (TM_Fun p P block R)
  .

Definition is_value t :=
  match t with
  | TM_Nil | TM_Num _ | TM_Arr _ _ | TM_Loc _ | TM_Fun _ _ _ _ => true
  | _ => false
  end.

Lemma value_equivalence : forall t,
  value t <-> is_value t = true.
Proof.
  intros t. split; induction t; intros H;
  try inversion H; auto using is_value, value.
Qed.

(* Effects *)

Inductive effect : Set :=
  | EF_None
  | EF_Spawn (block : tm)
  | EF_Load (addr : num) (t : tm)
  | EF_Store (addr : num) (t : tm)
  .

(* Auxiliary Aliases *)

Definition ctx := map typ.
Definition mem := list tm.
Definition mem_typ := list typ.
Definition get_typ := get TY_Void.
Definition get_tm  := get TM_Nil.
Definition get_ctx := get (@empty typ).

(* Operational Semantics *)

Local Infix "=?" := String.eqb (at level 70, no associativity).

Fixpoint subst (id : name) (x t : tm) : tm :=
  match t with
  | TM_Nil => t
  | TM_Num _ => t
  | TM_Arr _ _ => t
  | TM_ArrNew T e =>
      TM_ArrNew T ([id := x] e)
  | TM_ArrIdx arr idx =>
      TM_ArrIdx ([id := x] arr) ([id := x] idx)
  | TM_Id id' =>
      if id =? id' then x else t
  | TM_Asg t' e =>
      TM_Asg ([id := x] t') ([id := x] e)
  | TM_ArrAsg arr idx e =>
      TM_ArrAsg ([id := x] arr) ([id := x] idx) ([id := x] e)
  | TM_Call f a =>
      TM_Call ([id := x] f) ([id := x] a)
  | TM_Seq t1 t2 =>
      TM_Seq ([id := x] t1) ([id := x] t2)
  | TM_Spawn block =>
      TM_Spawn ([id := x] block)
  | TM_LetVal id' E e t' =>
      TM_LetVal id' E ([id := x] e) (if id =? id' then t' else [id := x] t')
  | TM_LetVar id' E e t' =>
      TM_LetVar id' E ([id := x] e) (if id =? id' then t' else [id := x] t')
  | TM_LetFun id' F f t' => 
      TM_LetFun id' F ([id := x] f) (if id =? id' then t' else [id := x] t')
  | TM_Loc _ => t
  | TM_Load t' =>
      TM_Load ([id := x] t')
  | TM_Fun p P block R =>
      if id =? p then t else TM_Fun p P ([id := x] block) R
  end
  where "'[' id ':=' x ']' t" := (subst id x t).

Inductive step : tm -> tm -> effect -> Prop :=
(*
  (* ArrNew *)
  | ST_ArrNew1 : forall m m' T e e' eff,
    m / e --> eff / m' / e' ->
    m / TM_ArrNew T e --> eff / m' / TM_ArrNew T e'

  | ST_ArrNew : forall m T e,
    value e ->
    m / TM_ArrNew T e --> EF_None / (add m e) / TM_Arr T (length m)

  (* ArrIdx *)
  | ST_ArrIdx1 : forall m m' arr arr' idx eff,
    m / arr --> eff / m' / arr' ->
    m / TM_ArrIdx arr idx --> eff / m' / TM_ArrIdx arr' idx

  | ST_ArrIdx2 : forall m m' arr idx idx' eff,
    value arr ->
    m / idx --> eff / m' / idx' ->
    m / TM_ArrIdx arr idx --> eff / m' / TM_ArrIdx arr idx'

  | ST_ArrIdx : forall m T i j,
    m / TM_ArrIdx (TM_Arr T i) (TM_Num j) --> EF_None / m / (get_tm m i)
*)
  (* Asg *)
  | ST_Asg1 : forall t t' e eff,
    t --> t' # eff ->
    TM_Asg t e --> TM_Asg t' e # eff

  | ST_Asg2 : forall t e e' eff,
    value t ->
    e --> e' # eff ->
    TM_Asg t e --> TM_Asg t e' # eff

  | ST_Asg : forall addr v,
    value v ->
    TM_Asg (TM_Loc addr) v --> TM_Nil # EF_Store addr v
(*
  (* ArrAsg *)
  | ST_ArrAsg1 : forall m m' arr arr' idx e eff,
    m / arr --> eff / m' / arr' ->
    m / TM_ArrAsg arr idx e --> eff / m' / TM_ArrAsg arr' idx e

  | ST_ArrAsg2 : forall m m' arr idx idx' e eff,
    value arr ->
    m / idx --> eff / m' / idx' ->
    m / TM_ArrAsg arr idx e --> eff / m' / TM_ArrAsg arr idx' e

  | ST_ArrAsg3 : forall m m' arr idx e e' eff,
    value arr ->
    value idx ->
    m / e --> eff / m' / e' ->
    m / TM_ArrAsg arr idx e --> eff / m' / TM_ArrAsg arr idx e'

  | ST_ArrAsg : forall m T i idx e,
    value e ->
    value idx ->
    i < length m ->
    m / TM_ArrAsg (TM_Arr T i) idx e --> EF_None / (set m i e) / TM_Nil

  (* Call *)
  | ST_Call1 : forall m m' f f' a eff,
    m / f --> eff / m' / f' ->
    m / TM_Call f a --> eff / m' / TM_Call f' a

  | ST_Call2 : forall m m' f a a' eff,
    value f ->
    m / a --> eff / m' / a' ->
    m / TM_Call f a --> eff / m' / TM_Call f a'

  | ST_Call : forall m a p P block R,
    value a ->
    m / TM_Call (TM_Fun p P block R) a --> EF_None / m / [p := a] block
*)
  (* Seq *)
  | ST_Seq1 : forall t1 t2 t eff,
    t1 --> t2 # eff ->
    TM_Seq t1 t --> TM_Seq t2 t # eff

  | ST_Seq : forall t,
    TM_Seq TM_Nil t --> t # EF_None

  (* Spawn *)
  | ST_Spawn : forall block,
    TM_Spawn block --> TM_Nil # EF_Spawn block

  (* LetVal *)
  | ST_LetVal1 : forall id E e e' t eff,
    e --> e' # eff ->
    TM_LetVal id E e t --> TM_LetVal id E e' t # eff

  | ST_LetVal : forall id E e t,
    value e ->
    TM_LetVal id E e t --> [id := e] t # EF_None
(*
  (* LetVar *)
  | ST_LetVar1 : forall m m' id E e e' t eff,
    m / e --> eff / m' / e' ->
    m / TM_LetVar id E e t --> eff / m' / TM_LetVar id E e' t

  | ST_LetVar : forall m id E e t,
    value e ->
    m / TM_LetVar id E e t --> EF_None / (add m e) / [id := TM_Loc (length m)] t

  (* LetFun *)
  | ST_LetFun1 : forall m m' id F f f' t eff,
    m / f --> eff / m' / f' ->
    m / TM_LetFun id F f t --> eff / m' / TM_LetFun id F f' t

  | ST_LetFun : forall m id F f t,
    value f ->
    m / TM_LetFun id F f t --> EF_None / m / [id := f] t
*)
  (* Load *)
  | ST_Load1 : forall t t' eff,
    t --> t' # eff ->
    TM_Load t --> TM_Load t' # eff

  | ST_Load : forall t addr,
    TM_Load (TM_Loc addr) --> t # EF_Load addr t

  where "t '-->' t' # eff" := (step t t' eff).

Inductive multistep : tm -> tm -> Prop :=
  | multistep_refl : forall t,
    t -->* t

  | multistep_step : forall t1 t t2 eff,
    t1 -->  t  # eff ->
    t  -->* t2 ->
    t1 -->* t2

  where "t '-->*' t'" := (multistep t t').

Inductive multistep_plus : tm -> tm -> Prop :=
  | multistep_plus_one : forall t t' eff,
    t -->  t' # eff ->
    t -->+ t

  | multistep_plus_step : forall t1 t t2 eff,
    t1 -->  t  # eff ->
    t  -->+ t2 ->
    t1 -->+ t2

  where "t '-->+' t'" := (multistep_plus t t').

(* Concurrent Step *)

(*
* => m / threads ==> m' / threads' com i
* e depois com
* => m' / threads' ==> m'' / threads'' com j
*
*  m <--> m'' não escrevem na mesma célula de memória
*)

Inductive cstep : mem -> list tm -> mem -> list tm -> Prop :=
  | CST_None : forall i m t ths,
    i < length ths ->
    (get_tm ths i) --> t # EF_None ->
    m / ths ==> m / (set ths i t)

  | CST_Load : forall i m ths addr v,
    i < length ths ->
    v = get_tm m addr ->
    (get_tm ths i) --> v # (EF_Load addr v) ->
    m / ths ==> m / (set ths i v)

  | CST_Store : forall i m ths addr v t,
    i < length ths ->
    addr < length m ->
    (get_tm ths i) --> t # (EF_Store addr v) ->
    m / ths ==> (set m addr v) / (set ths i t)

  | CST_Spawn : forall i m ths block t,
    i < length ths ->
    (get_tm ths i) --> t # (EF_Spawn block) ->
    m / ths ==> m / (add (set ths i t) block)

  where "m / threads '==>' m' / threads'" := (cstep m threads m' threads').

Inductive cmultistep : mem -> list tm -> mem -> list tm -> Prop :=
  | cmultistep_refl : forall m ths,
    m / ths ==>* m / ths

  | cmultistep_step : forall m1 m m2 ths1 ths ths2,
    m1 / ths1 ==>  m  / ths  ->
    m  / ths  ==>* m2 / ths2 ->
    m1 / ths1 ==>* m2 / ths2

  where "m / ths '==>*' m' / ths'" := (cmultistep m ths m' ths').

(* Typing *)

Inductive typeof {mt : mem_typ} : ctx -> tm -> typ -> Prop :=
  | T_Nil : forall Gamma,
    Gamma |-- TM_Nil is TY_Void

  | T_Num : forall Gamma n,
    Gamma |-- (TM_Num n) is TY_Num

  | T_Arr : forall Gamma T i,
    T = get_typ mt i ->
    i < length mt ->
    Gamma |-- (TM_Arr (TY_Arr T) i) is (TY_Arr T)

  | T_IArr : forall Gamma T i,
    T = get_typ mt i ->
    i < length mt ->
    Gamma |-- (TM_Arr (TY_IArr T) i) is (TY_IArr T)

  | T_ArrNew : forall Gamma e E,
    Gamma |-- e is E ->
    Gamma |-- (TM_ArrNew (TY_Arr E) e) is (TY_Arr E)

  | T_IArrNew : forall Gamma e E,
    Gamma |-- e is E -> (* immutable *)
    Gamma |-- (TM_ArrNew (TY_IArr E) e) is (TY_IArr E)

  | T_ArrIdx : forall Gamma arr idx T,
    Gamma |-- arr is (TY_Arr T) ->
    Gamma |-- idx is TY_Num ->
    Gamma |-- (TM_ArrIdx arr idx) is T

  | T_IArrIdx : forall Gamma arr idx T,
    Gamma |-- arr is (TY_IArr T) ->
    Gamma |-- idx is TY_Num ->
    Gamma |-- (TM_ArrIdx arr idx) is T

  | T_Id_Val : forall Gamma id T,
    lookup Gamma id = Some (TY_IRef T) ->
    Gamma |-- (TM_Id id) is (TY_IRef T)

  | T_Id_Var : forall Gamma id T,
    lookup Gamma id = Some (TY_Ref T) ->
    Gamma |-- (TM_Id id) is (TY_Ref T)

  | T_Asg : forall Gamma t e T,
    Gamma |-- t is (TY_Ref T) ->
    Gamma |-- e is T ->
    Gamma |-- (TM_Asg t e) is TY_Void

  | T_ArrAsg : forall Gamma arr idx e E,
    Gamma |-- arr is (TY_Arr E) ->
    Gamma |-- idx is TY_Num ->
    Gamma |-- e is E ->
    Gamma |-- (TM_ArrAsg arr idx e) is TY_Void

  | T_Call : forall Gamma f a P R,
    Gamma |-- f is (TY_Fun P R) ->
    Gamma |-- a is P ->
    Gamma |-- (TM_Call f a) is R

  | T_Seq : forall Gamma t t' T,
    Gamma |-- t  is TY_Void ->
    Gamma |-- t' is T ->
    Gamma |-- (TM_Seq t t') is T

  | T_Spawn : forall Gamma block T,
    safe Gamma |-- block is T ->
    Gamma |-- (TM_Spawn block) is TY_Void

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
    safe Gamma |-- f is F ->
    (update Gamma id F) |-- t is T ->
    Gamma |-- (TM_LetFun id F f t) is T

  | T_Loc : forall Gamma i,
    i < length mt ->
    Gamma |-- (TM_Loc i) is TY_Ref (get_typ mt i)

  | T_Load_Ref : forall Gamma t T,
    Gamma |-- t is TY_Ref T ->
    Gamma |-- (TM_Load t) is T

  | T_Load_IRef : forall Gamma t T,
    Gamma |-- t is TY_IRef T ->
    Gamma |-- (TM_Load t) is T

  | T_Fun : forall Gamma p P block R,
    (update Gamma p P) |-- block is R ->
    Gamma |-- (TM_Fun p P block R) is (TY_Fun P R)

  where "Gamma '|--' t 'is' T" := (typeof Gamma t T)
  and "mt / Gamma '|--' t 'is' T" := (@typeof mt Gamma t T).

(* Threads *)

(*
From Coq Require Import String.
Open Scope string_scope.

Definition x := "x".
Definition letX := TM_LetVal x TY_Num (TM_Num 10) (TM_Id x).
Definition stepLetX := ST_LetVal nil x TY_Num (TM_Num 10) (TM_Id x) (V_Num 10).
Definition threads := letX :: letX :: nil.
Example notConc : ~ (ctm letX). intros H. inversion H. Qed.

Theorem not_deterministic_cstep : ~ (deterministic cstep).
Proof.
  unfold not, deterministic. intros H.
  specialize (H nil nil threads [letX ; TM_Num 10] [TM_Num 10 ; letX]).
  specialize (H (CST_Thread 1 _ _ threads _ _ eq_refl notConc stepLetX)).
  specialize (H (CST_Thread 0 _ _ threads _ _ eq_refl notConc stepLetX)).
  discriminate H.
Qed.

Close Scope string_scope.
*)

(*

"i" é um índice na memória.

TM_NewMtx => Cria um mutex na memória com mem[i] = 0.

TM_Mtx i => Se o valor de mem[i] for 0 então pode entrar no mutex.
            Se não, tem alguém no mutex.

CST_AcqMtx_Ok
  get_tm m i = 0
  m / TM_AcqMtx (TM_Mtx i) --> (set_tm m i 1) / TM_Nil

(* busy waiting *)
CST_AcqMtx_NotOk
  get_tm m i = 1
  m / TM_AcqMtx (TM_Mtx i) --> m / TM_Seq TM_Nil (TM_AcqMtx (TM_Mtx i))

*)
