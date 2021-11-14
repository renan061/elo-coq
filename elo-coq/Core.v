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
Reserved Notation "m / t '-->' m' / t'"
  (at level 40, t at next level, m' at next level).
Reserved Notation "m / t '-->*' m' / t'"
  (at level 40, t at next level, m' at next level).
Reserved Notation "m / t '-->+' m' / t'"
  (at level 40, t at next level, m' at next level).
Reserved Notation "m / threads '==>' m' / threads'"
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
  (* definitions *)
  | TM_LetVal : name -> typ -> tm -> tm -> tm
  | TM_LetVar : name -> typ -> tm -> tm -> tm
  | TM_LetFun : name -> typ -> tm -> tm -> tm
  (* internal terms *)
  | TM_Loc : nat -> tm
  | TM_Load : tm -> tm
  | TM_Fun : name -> typ -> tm -> typ -> tm
  .

(*
  | TM_LetMon : name -> monitor -> tm
  | TM_Mon : monitor -> tm
with monitor : Set :=
  | MonitorNil
  | MonitorVal : name -> typ -> tm -> tm -> mon -> mon
  | MonitorVar : name -> typ -> tm -> tm -> mon -> mon
  | MonitorFun : name -> typ -> tm -> tm -> mon -> mon
  .
*)

(* Values *)

Inductive value : tm -> Prop :=
  | V_Nil : value TM_Nil
  | V_Num : forall n, value (TM_Num n)
  | V_Arr : forall T i, value (TM_Arr T i)
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

Inductive step : mem -> tm -> mem -> tm -> Prop :=
  (* ArrNew *)
  | ST_ArrNew1 : forall m m' T e e',
    m / e --> m' / e' ->
    m / TM_ArrNew T e --> m' / TM_ArrNew T e'

  | ST_ArrNew : forall m T e,
    value e ->
    m / TM_ArrNew T e --> (add m e) / TM_Arr T (length m)

  (* ArrIdx *)
  | ST_ArrIdx1 : forall m m' arr arr' idx,
    m / arr --> m' / arr' ->
    m / TM_ArrIdx arr idx --> m' / TM_ArrIdx arr' idx

  | ST_ArrIdx2 : forall m m' arr idx idx',
    value arr ->
    m / idx --> m' / idx' ->
    m / TM_ArrIdx arr idx --> m' / TM_ArrIdx arr idx'

  | ST_ArrIdx : forall m T i j,
    m / TM_ArrIdx (TM_Arr T i) (TM_Num j) --> m / (get_tm m i)

  (* Asg *)
  | ST_Asg1 : forall m m' t t' e,
    m / t --> m' / t' ->
    m / TM_Asg t e --> m' / TM_Asg t' e

  | ST_Asg2 : forall m m' t e e',
    value t ->
    m / e --> m' / e' ->
    m / TM_Asg t e --> m' / TM_Asg t e'

  | ST_Asg : forall m i e,
    value e ->
    i < length m ->
    m / TM_Asg (TM_Loc i) e --> (set m i e) / TM_Nil

  (* ArrAsg *)
  | ST_ArrAsg1 : forall m m' arr arr' idx e,
    m / arr --> m' / arr' ->
    m / TM_ArrAsg arr idx e --> m' / TM_ArrAsg arr' idx e

  | ST_ArrAsg2 : forall m m' arr idx idx' e,
    value arr ->
    m / idx --> m' / idx' ->
    m / TM_ArrAsg arr idx e --> m' / TM_ArrAsg arr idx' e

  | ST_ArrAsg3 : forall m m' arr idx e e',
    value arr ->
    value idx ->
    m / e --> m' / e' ->
    m / TM_ArrAsg arr idx e --> m' / TM_ArrAsg arr idx e'

  | ST_ArrAsg : forall m T i idx e,
    value e ->
    value idx ->
    i < length m ->
    m / TM_ArrAsg (TM_Arr T i) idx e --> (set m i e) / TM_Nil

  (* Call *)
  | ST_Call1 : forall m m' f f' a,
    m / f --> m' / f' ->
    m / TM_Call f a --> m' / TM_Call f' a

  | ST_Call2 : forall m m' f a a',
    value f ->
    m / a --> m' / a' ->
    m / TM_Call f a --> m' / TM_Call f a'

  | ST_Call : forall m a p P block R,
    value a ->
    m / TM_Call (TM_Fun p P block R) a --> m / [p := a] block

  (* Seq *)
  | ST_Seq1 : forall m m' t1 t2 t,
    m / t1 --> m' / t2 ->
    m / TM_Seq t1 t --> m' / TM_Seq t2 t

  | ST_Seq : forall m t,
    m / TM_Seq TM_Nil t --> m / t

  (* LetVal *)
  | ST_LetVal1 : forall m m' id E e e' t,
    m / e --> m' / e' ->
    m / TM_LetVal id E e t --> m' / TM_LetVal id E e' t

  | ST_LetVal : forall m id E e t,
    value e ->
    m / TM_LetVal id E e t --> m / [id := e] t

  (* LetVar *)
  | ST_LetVar1 : forall m m' id E e e' t,
    m / e --> m' / e' ->
    m / TM_LetVar id E e t --> m' / TM_LetVar id E e' t

  | ST_LetVar : forall m id E e t,
    value e ->
    m / TM_LetVar id E e t --> (add m e) / [id := TM_Loc (length m)] t

  (* LetFun *)
  | ST_LetFun1 : forall m m' id F f f' t,
    m / f --> m' / f' ->
    m / TM_LetFun id F f t --> m' / TM_LetFun id F f' t

  | ST_LetFun : forall m id F f t,
    value f ->
    m / TM_LetFun id F f t --> m / [id := f] t

  (* Load *)
  | ST_Load1 : forall m m' t t',
    m / t --> m' / t' ->
    m / TM_Load t --> m' / TM_Load t'

  | ST_Load : forall m i,
    m / TM_Load (TM_Loc i) --> m / (get_tm m i)

  where "m / t '-->' m' / t'" := (step m t m' t').

Inductive multistep : mem -> tm -> mem -> tm -> Prop :=
  | multistep_refl : forall m t,
    m / t -->* m / t

  | multistep_step : forall m1 m m2 t1 t t2,
    m1 / t1 -->  m  / t  ->
    m  / t  -->* m2 / t2 ->
    m1 / t1 -->* m2 / t2

  where "m / t '-->*' m' / t'" := (multistep m t m' t').

Inductive multistep_plus : mem -> tm -> mem -> tm -> Prop :=
  | multistep_plus_one : forall m m' t t',
    m / t -->  m' / t' ->
    m / t -->+ m  / t

  | multistep_plus_step : forall m1 m m2 t1 t t2,
    m1 / t1 -->  m  / t  ->
    m  / t  -->+ m2 / t2 ->
    m1 / t1 -->+ m2 / t2

  where "m / t '-->+' m' / t'" := (multistep_plus m t m' t').

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
    (* safe *) Gamma |-- f is F ->
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

Inductive ttm : Set :=
  | TTM_Spawn : ttm -> ttm
  | TTM_Wait : ttm -> ttm -> ttm
  | TTM_Signal : ttm -> ttm
  | TTM_Broadcast : ttm -> ttm
  | TTM_AcquireVal
  .

(* TODO *)

Fixpoint count {A} (m : map A) k :=
  match m with
  | map_nil _ => 0
  | map_cons _ k' _ m' =>
    if k =? k'
      then 1 + count m' k
      else count m' k
  end.

Definition contains {A} (m : map A) k :=
  match lookup m k with None => false | Some _ => true end.

Definition unique_map {A} (m : map A) :=
  forall k v, lookup m k = Some v -> count m k = 1.

(* auxiliary function *)
Local Fixpoint f {A} (m acc : map A) : map A :=
  match m with
  | map_nil _ => acc
  | map_cons _ k v m' => f m' (if contains acc k then acc else update acc k v)
  end.

Definition make_unique_map {A} (m : map A) : map A := f m empty.

Theorem make_unique_map_correct : forall {A} (m : map A),
  unique_map (make_unique_map m).
Proof.
  unfold unique_map, make_unique_map, f. intros *.
  induction m as [| k' v' m' IH].
  - intros H. unfold f, empty, lookup in H. discriminate H.
  - fold (@f A) in *. unfold update in *.
    assert (H1 : @contains A empty k' = false). { reflexivity. }
    rewrite H1. clear H1. intros H.
Admitted.

Theorem unique_map_equivalence : forall {A} (m : map A) k v,
  lookup m k = Some v <-> lookup (make_unique_map m) k = Some v.
Admitted.

Inductive safe_type : typ -> Prop :=
  | S_Void : safe_type TY_Void
  | S_Num  : safe_type TY_Num
  | S_IArr : forall T, safe_type T -> safe_type (TY_IArr T)
  | S_IRef : forall T, safe_type T -> safe_type (TY_IRef T)
  | S_Fun  : forall P R, safe_type (TY_Fun P R)
  .

Fixpoint safe_type_bool T :=
  match T with
  | TY_Void | TY_Num | TY_Fun _ _ => true
  | TY_IArr T' | TY_IRef T' => safe_type_bool T'
  | _ => false
  end.

Theorem safe_type_equivalence : forall T,
  safe_type T <-> safe_type_bool T = true.
Admitted.

Definition safe_context Gamma :=
  forall id T, lookup Gamma id = Some T -> safe_type T.

Fixpoint make_safe_context (c : ctx) : ctx :=
  match c with
  | map_nil _ => map_nil typ
  | map_cons _ id T c' =>
      if safe_type_bool T
        then map_cons typ id T (make_safe_context c')
        else make_safe_context c'
  end.

Theorem make_safe_context_is_correct : forall Gamma,
  safe_context (make_safe_context Gamma).
Proof.
  unfold safe_context. intros Gamma id T.
  induction Gamma.
  - unfold make_safe_context, lookup. discriminate.
  - destruct (safe_type_bool v) eqn:E;
    unfold make_safe_context in *;
    rewrite E in *;
    fold make_safe_context in *;
    trivial.
    unfold lookup in *.
    destruct (String.eqb k id).
    + intros H. injection H as ?. subst.
      apply safe_type_equivalence. assumption.
    + fold (@lookup typ) in *. auto.
Qed.

Definition safe Gamma := make_safe_context (make_unique_map Gamma).

Theorem safe_is_correctness : forall Gamma,
  safe_context (safe Gamma).
Proof.
Admitted.

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

Inductive ctm : tm -> Prop :=
  (*
  | CTM_Spawn : forall block, ctm (TM_Spawn block)
  | CTM_Wait
  | CTM_Signal
  | CTM_Broadcast
  | CTM_AcquireVal
  *)
  .

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

(* Inductive cstep : mem -> list tm -> mem -> list tm -> Prop :=
  | CST_Thread : forall i m m' threads t t',
    t = get_tm threads i ->
    ~ (ctm t) ->
    m / t --> m' / t' ->
    m / threads ==> m' / (set threads i t')

  | CST_Spawn : forall i m m' threads t t' block,
    t = get_tm threads i ->
    t = TM_Spawn block ->
    m / t --> m' / t' ->
    m / threads ==> m' / (add (set threads i t') block)

  where "m / threads '==>' m' / threads'" := (cstep m threads m' threads').
 *)
(* Typing *)

(* Definition safe_context (Gamma new : ctx) : ctx :=
  match Gamma with
  | fun x => _ => new
  end. *)
