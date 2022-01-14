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
Reserved Notation "t '--[' eff ']-->' t'"
  (at level 40).
Reserved Notation "m / ths '==>' m' / ths' # ceff"
  (at level 40, ths at next level, m' at next level).
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

Definition safe (Gamma : map typ) :=
  fun k => 
    match Gamma k with
    | None => None
    | Some T => if is_safe_type T then Some T else None
    end.

(* Terms *)

Inductive tm : Set :=
  (* expressions *)
  | TM_Nil
  | TM_Num : num -> tm
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
  | TM_Arr : typ -> num -> tm (* TODO: ordering *)
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

(* Effects *)

Inductive effect : Set :=
  | EF_None
  | EF_Spawn (block : tm)
  | EF_Alloc (addr : num) (t : tm)
  | EF_Load  (addr : num) (t : tm)
  | EF_Store (addr : num) (t : tm)
  .

(* Auxiliary Aliases *)

Definition ctx := map typ.
Definition mem := list tm.
Definition threads := list tm.
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

Inductive step : tm -> effect -> tm -> Prop :=
  (* ArrNew *)
  | ST_ArrNew1 : forall T e e' eff,
    e --[eff]--> e' ->
    TM_ArrNew T e --[eff]--> TM_ArrNew T e'

  | ST_ArrNew : forall T addr v,
    value v ->
    TM_ArrNew T v --[EF_Alloc addr v]--> TM_Arr T addr

  (* ArrIdx *)
  | ST_ArrIdx1 : forall arr arr' idx eff,
    arr --[eff]--> arr' ->
    TM_ArrIdx arr idx --[eff]--> TM_ArrIdx arr' idx

  | ST_ArrIdx2 : forall arr idx idx' eff,
    value arr ->
    idx --[eff]--> idx' ->
    TM_ArrIdx arr idx --[eff]--> TM_ArrIdx arr idx'

  | ST_ArrIdx : forall T addr idx,
    TM_ArrIdx (TM_Arr T addr) (TM_Num idx) --[EF_None]--> TM_Load (TM_Loc addr)

  (* Asg *)
  | ST_Asg1 : forall t t' e eff,
    t --[eff]--> t' ->
    TM_Asg t e --[eff]--> TM_Asg t' e

  | ST_Asg2 : forall t e e' eff,
    value t ->
    e --[eff]--> e' ->
    TM_Asg t e --[eff]--> TM_Asg t e'

  | ST_Asg : forall addr v,
    value v ->
    TM_Asg (TM_Loc addr) v --[EF_Store addr v]--> TM_Nil

  (* ArrAsg *)
  | ST_ArrAsg1 : forall arr arr' idx e eff,
    arr --[eff]--> arr' ->
    TM_ArrAsg arr idx e --[eff]--> TM_ArrAsg arr' idx e

  | ST_ArrAsg2 : forall arr idx idx' e eff,
    value arr ->
    idx --[eff]--> idx' ->
    TM_ArrAsg arr idx e --[eff]--> TM_ArrAsg arr idx' e

  | ST_ArrAsg3 : forall arr idx e e' eff,
    value arr ->
    value idx ->
    e --[eff]--> e' ->
    TM_ArrAsg arr idx e --[eff]--> TM_ArrAsg arr idx e'

  | ST_ArrAsg : forall T addr idx v,
    value v ->
    value idx ->
    TM_ArrAsg (TM_Arr T addr) idx v --[EF_None]--> TM_Asg (TM_Loc addr) v

  (* Call *)
  | ST_Call1 : forall f f' a eff,
    f --[eff]--> f' ->
    TM_Call f a --[eff]--> TM_Call f' a

  | ST_Call2 : forall f a a' eff,
    value f ->
    a --[eff]--> a' ->
    TM_Call f a --[eff]--> TM_Call f a'

  | ST_Call : forall p P block R a,
    value a ->
    TM_Call (TM_Fun p P block R) a --[EF_None]--> [p := a] block

  (* Seq *)
  | ST_Seq1 : forall t1 t2 t eff,
    t1 --[eff]--> t2 ->
    TM_Seq t1 t --[eff]--> TM_Seq t2 t

  | ST_Seq : forall t,
    TM_Seq TM_Nil t --[EF_None]--> t

  (* Spawn *)
  | ST_Spawn : forall block,
    TM_Spawn block --[EF_Spawn block]--> TM_Nil

  (* LetVal *)
  | ST_LetVal1 : forall id E e e' t eff,
    e --[eff]--> e' ->
    TM_LetVal id E e t --[eff]--> TM_LetVal id E e' t

  | ST_LetVal : forall id E e t,
    value e ->
    TM_LetVal id E e t --[EF_None]--> [id := e] t

  (* LetVar *)
  | ST_LetVar1 : forall id E e e' t eff,
    e --[eff]--> e' ->
    TM_LetVar id E e t --[eff]--> TM_LetVar id E e' t

  | ST_LetVar : forall id E addr e t,
    value e ->
    TM_LetVar id E e t --[EF_Alloc addr e]--> [id := TM_Loc addr] t

  (* LetFun *)
  | ST_LetFun1 : forall id F f f' t eff,
    f --[eff]--> f' ->
    TM_LetFun id F f t --[eff]--> TM_LetFun id F f' t

  | ST_LetFun : forall id F f t,
    value f ->
    TM_LetFun id F f t --[EF_None]--> [id := f] t

  (* Load *)
  | ST_Load1 : forall t t' eff,
    t --[eff]--> t' ->
    TM_Load t --[eff]--> TM_Load t'

  | ST_Load : forall addr v,
    TM_Load (TM_Loc addr) --[EF_Load addr v]--> v

  where "t '--[' eff ']-->' t'" := (step t eff t').

(* Concurrent Step *)

Inductive ceffect : Set :=
  | CEF_None  (i : num)
  | CEF_Alloc (i : num) (addr : num)
  | CEF_Load  (i : num) (addr : num)
  | CEF_Store (i : num) (addr : num)
  | CEF_Spawn (i : num)
  .

Inductive cstep : mem -> threads -> mem -> threads -> ceffect -> Prop :=
  | CST_None : forall i m ths t,
    i < length ths ->
    (get_tm ths i) --[EF_None]--> t ->
    m / ths ==> m / (set ths i t) # (CEF_None i)

  | CST_Alloc : forall i m ths v t,
    i < length ths ->
    (get_tm ths i) --[EF_Alloc (length m) v]--> t ->
    m / ths ==> (add m v) / (set ths i t) # (CEF_Alloc i (length m))

  | CST_Load : forall i m ths addr t,
    i < length ths ->
    (get_tm ths i) --[EF_Load addr (get_tm m addr)]--> t ->
    m / ths ==> m / (set ths i t) # (CEF_Load i addr)

  | CST_Store : forall i m ths addr v t,
    i < length ths ->
    addr < length m ->
    (get_tm ths i) --[EF_Store addr v]--> t ->
    m / ths ==> (set m addr v) / (set ths i t) # (CEF_Store i addr)

  | CST_Spawn : forall i m ths block t,
    i < length ths ->
    (get_tm ths i) --[EF_Spawn block]--> t ->
    m / ths ==> m / (add (set ths i t) block) # (CEF_Spawn i)

  where "m / ths '==>' m' / ths' # ceff" := (cstep m ths m' ths' ceff).

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
