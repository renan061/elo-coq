From Coq Require Import Init.Nat.
From Coq Require Import List.

From Elo Require Import Array.
From Elo Require Import Map.

Import ListNotations.

Definition name := String.string.
Definition num := nat.

(* Notations *)

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
  .

(* Terms *)

Inductive tm : Set :=
  | TM_Nil
  | TM_Num  : num -> tm
  | TM_Loc  : num -> tm
  | TM_New  : tm -> tm
  | TM_Load : tm -> tm
  | TM_Asg  : tm -> tm -> tm
  .

(* Values *)

Inductive value : tm -> Prop :=
  | V_Nil : value TM_Nil
  | V_Num : forall n, value (TM_Num n)
  | V_Loc : forall i, value (TM_Loc i)
  .

(* Effects *)
Definition addr := nat.

Inductive effect : Set :=
  | EF_None
  | EF_Alloc (ad : addr) (t : tm)
  | EF_Load  (ad : addr) (t : tm)
  | EF_Store (ad : addr) (t : tm)
  .

(* Auxiliary Aliases *)

Definition ctx := map typ.
Definition mem := list tm.
(* Definition threads := list tm. *)
Definition memtyp := list typ.
Definition get_typ := get TY_Void.
Definition get_tm  := get TM_Nil.
Definition get_ctx := get (@empty typ).

(* Operational Semantics *)

Inductive step : tm -> effect -> tm -> Prop :=
  (* New *)
  | ST_New1 : forall t t' eff,
    t --[eff]--> t' ->
    TM_New t --[eff]--> t'

  | ST_New : forall t ad,
    value t ->
    TM_New t --[EF_Alloc ad t]--> TM_Loc ad

  (* Load *)
  | ST_Load1 : forall t t' eff,
    t --[eff]--> t' ->
    TM_Load t --[eff]--> TM_Load t'

  | ST_Load : forall ad t,
    TM_Load (TM_Loc ad) --[EF_Load ad t]--> t

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

  where "t '--[' eff ']-->' t'" := (step t eff t').

(* Memory Step *)

Inductive mstep : mem -> tm -> effect -> mem -> tm -> Prop :=
  | MST_Alloc : forall m t t' v,
    t --[EF_Alloc (length m) v]--> t' ->
    m / t ==[ EF_Alloc (length m) v ]==> (add m v) / t'

  | MST_Load : forall m t t' ad,
    t --[EF_Load ad (get_tm m ad)]--> t' ->
    m / t ==[ EF_Load ad (get_tm m ad) ]==> m / t'

  | MST_Store : forall m t t' ad v,
    ad < length m ->
    t --[EF_Store ad v]--> t' ->
    m / t ==[ EF_Store ad v ]==> (set m ad v) / t'

  where "m / t '==[' eff ']==>' m' / t'" := (mstep m t eff m' t').

(* Typing *)

Inductive well_typed_term (mt : memtyp) : ctx -> tm -> typ -> Prop :=
  | T_Nil : forall Gamma,
    mt / Gamma |-- TM_Nil is TY_Void

  | T_Num : forall Gamma n,
    mt / Gamma |-- (TM_Num n) is TY_Num

  | T_Loc : forall Gamma ad,
    ad < length mt ->
    mt / Gamma |-- (TM_Loc ad) is TY_Ref (get_typ mt ad)

  | T_New : forall Gamma t T,
    mt / Gamma |-- t is T ->
    mt / Gamma |-- (TM_New t) is (TY_Ref T)

  | T_Load : forall Gamma t T,
    mt / Gamma |-- t is TY_Ref T ->
    mt / Gamma |-- (TM_Load t) is T

  | T_Asg : forall Gamma l r T,
    mt / Gamma |-- l is (TY_Ref T) ->
    mt / Gamma |-- r is T ->
    mt / Gamma |-- (TM_Asg l r) is TY_Void

  where "mt / Gamma '|--' t 'is' T" := (well_typed_term mt Gamma t T).
