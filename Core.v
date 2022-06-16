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
Reserved Notation "m / ths '==[' ceff ']==>' m' / ths'"
  (at level 40, ths at next level, ceff at next level, m' at next level).
Reserved Notation "mt / Gamma '|--' t 'is' T"
  (at level 40, Gamma at next level).

(* Types *)

Inductive typ : Set :=
  | TY_Void
  | TY_Num
  | TY_Ref : typ -> typ
  | TY_Fun : typ -> typ -> typ
  .

(* Terms *)

Inductive tm : Set :=
  | TM_Nil
  | TM_Num : num -> tm
  | TM_Id : name -> tm
  | TM_Fun : name -> typ -> tm -> typ -> tm
  | TM_Loc : num -> tm
  | TM_Load : tm -> tm
  | TM_New : tm -> tm
  | TM_Asg : tm -> tm -> tm
  | TM_Call : tm -> tm -> tm
  | TM_Seq : tm -> tm -> tm
  | TM_Let : name -> typ -> tm -> tm -> tm
  .

(* Values *)

Inductive value : tm -> Prop :=
  | V_Nil : value TM_Nil
  | V_Num : forall n, value (TM_Num n)
  | V_Loc : forall i, value (TM_Loc i)
  | V_Fun : forall p P block R, value (TM_Fun p P block R)
  .

(* Effects *)

Inductive effect : Set :=
  | EF_None
  | EF_Alloc (ad : num) (t : tm)
  | EF_Load  (ad : num) (t : tm)
  | EF_Store (ad : num) (t : tm)
  .

Inductive ceffect : Set :=
  | CEF_None  (tid : nat)
  | CEF_Alloc (tid : nat) (ad : nat) (t : tm)
  | CEF_Load  (tid : nat) (ad : nat) (t : tm)
  | CEF_Store (tid : nat) (ad : nat) (t : tm)
  .

(* Auxiliary Aliases *)

Definition ctx := map typ.
Definition mem := list tm.
Definition threads := list tm.
Definition memtyp := list typ.
Definition get_typ := get TY_Void.
Definition get_tm  := get TM_Nil.
Definition get_ctx := get (@empty typ).

(* Operational Semantics *)

Local Infix "=?" := String.eqb (at level 70, no associativity).

Fixpoint subst (id : name) (x t : tm) : tm :=
  match t with
  | TM_Nil => t
  | TM_Num _ => t
  | TM_Id id' =>
      if id =? id' then x else t
  | TM_Fun p P block R =>
      if id =? p then t else TM_Fun p P ([id := x] block) R
  | TM_New t' =>
      [id := x] t'
  | TM_Loc _ => t
  | TM_Load t' =>
      TM_Load ([id := x] t')
  | TM_Asg t' e =>
      TM_Asg ([id := x] t') ([id := x] e)
  | TM_Call f a =>
      TM_Call ([id := x] f) ([id := x] a)
  | TM_Seq t1 t2 =>
      TM_Seq ([id := x] t1) ([id := x] t2)
  | TM_Let id' E e t' =>
      TM_Let id' E ([id := x] e) (if id =? id' then t' else [id := x] t')
  end
  where "'[' id ':=' x ']' t" := (subst id x t).

Inductive step : tm -> effect -> tm -> Prop :=
  (* Load *)
  | ST_Load1 : forall t t' eff,
    t --[eff]--> t' ->
    TM_Load t --[eff]--> TM_Load t'

  | ST_Load : forall ad t,
    TM_Load (TM_Loc ad) --[EF_Load ad t]--> t

  (* New *)
  | ST_New1 : forall t t' eff,
    t --[eff]--> t' ->
    TM_New t --[eff]--> t'

  | ST_New : forall t ad,
    value t ->
    TM_New t --[EF_Alloc ad t]--> TM_Loc ad

  (* Asg *)
  | ST_Asg1 : forall l l' r eff,
    l --[eff]--> l' ->
    TM_Asg l r --[eff]--> TM_Asg l' r

  | ST_Asg2 : forall l r r' eff,
    value l ->
    r --[eff]--> r' ->
    TM_Asg l r --[eff]--> TM_Asg l r'

  | ST_Asg : forall t ad,
    value t ->
    TM_Asg (TM_Loc ad) t --[EF_Store ad t]--> TM_Nil

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

  (* Let *)
  | ST_Let1 : forall id E e e' t eff,
    e --[eff]--> e' ->
    TM_Let id E e t --[eff]--> TM_Let id E e' t

  | ST_Let : forall id E e t,
    value e ->
    TM_Let id E e t --[EF_None]--> [id := e] t

  where "t '--[' eff ']-->' t'" := (step t eff t').

(* Concurrent Step *)

Inductive cstep : mem -> threads -> mem -> threads -> ceffect -> Prop :=
  | CST_None : forall tid m ths t,
    tid < length ths ->
    (get_tm ths tid) --[EF_None]--> t ->
    m / ths ==[ CEF_None tid ]==> m / (set ths tid t)

  | CST_Alloc : forall tid m ths v t,
    tid < length ths ->
    (get_tm ths tid) --[EF_Alloc (length m) v]--> t ->
    m / ths ==[ CEF_Alloc tid (length m) v ]==> (add m v) / (set ths tid t)

  | CST_Load : forall tid m ths ad t,
    tid < length ths ->
    (get_tm ths tid) --[EF_Load ad (get_tm m ad)]--> t ->
    m / ths ==[ CEF_Load tid ad (get_tm m ad) ]==> m / (set ths tid t)

  | CST_Store : forall tid m ths ad v t,
    tid < length ths ->
    ad < length m ->
    (get_tm ths tid) --[EF_Store ad v]--> t ->
    m / ths ==[ CEF_Store tid ad v ]==> (set m ad v) / (set ths tid t)

  where "m / ths '==[' ceff ']==>' m' / ths'" := (cstep m ths m' ths' ceff).

(* Typing *)

Inductive well_typed_term (mt : memtyp) : ctx -> tm -> typ -> Prop :=
  | T_Nil : forall Gamma,
    mt / Gamma |-- TM_Nil is TY_Void

  | T_Num : forall Gamma n,
    mt / Gamma |-- (TM_Num n) is TY_Num

  | T_Id : forall Gamma id T,
    lookup Gamma id = Some T ->
    mt / Gamma |-- (TM_Id id) is T

  | T_Fun : forall Gamma p P block R,
    mt / (update Gamma p P) |-- block is R ->
    mt / Gamma |-- (TM_Fun p P block R) is (TY_Fun P R)

  | T_Loc : forall Gamma ad,
    ad < length mt ->
    mt / Gamma |-- (TM_Loc ad) is TY_Ref (get_typ mt ad)

  | T_Load : forall Gamma t T,
    mt / Gamma |-- t is TY_Ref T ->
    mt / Gamma |-- (TM_Load t) is T

  | T_New : forall Gamma t T,
    mt / Gamma |-- t is T ->
    mt / Gamma |-- (TM_New t) is (TY_Ref T)

  | T_Asg : forall Gamma t e T,
    mt / Gamma |-- t is (TY_Ref T) ->
    mt / Gamma |-- e is T ->
    mt / Gamma |-- (TM_Asg t e) is TY_Void

  | T_Call : forall Gamma f a P R,
    mt / Gamma |-- f is (TY_Fun P R) ->
    mt / Gamma |-- a is P ->
    mt / Gamma |-- (TM_Call f a) is R

  | T_Seq : forall Gamma t t' T,
    mt / Gamma |-- t  is TY_Void ->
    mt / Gamma |-- t' is T ->
    mt / Gamma |-- (TM_Seq t t') is T

  | T_Let : forall Gamma id e t E T,
    mt / Gamma |-- e is E ->
    mt / (update Gamma id E) |-- t is T ->
    mt / Gamma |-- (TM_Let id E e t) is T

  where "mt / Gamma '|--' t 'is' T" := (well_typed_term mt Gamma t T).

