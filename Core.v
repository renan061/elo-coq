From Coq Require Import List.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
 
Definition id := Strings.String.string.
Definition num := nat.

(* Notations *)

Reserved Notation "'[' id ':=' x ']' t"
  (at level 20, id constr).
Reserved Notation "t '--[' eff ']-->' t'"
  (at level 40).
Reserved Notation "m / t '==[' eff ']==>' m' / t'"
  (at level 40, t at next level, eff at next level, m' at next level).
Reserved Notation "m / ths '~~[' tid , eff ']~~>' m' / ths'"
  (at level 40, ths at next level, tid at next level, eff at next level,
                m' at next level).
Reserved Notation "Gamma '|--' t 'is' T"
  (at level 40).

(* Types *)

Inductive typ : Set :=
  | TY_Unit
  | TY_Num
  | TY_RefM : typ -> typ
  | TY_RefI : typ -> typ
  | TY_Fun : typ -> typ -> typ
  .

Theorem typ_eq_dec : forall (t1 t2 : typ),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros. decide equality; eauto.
Qed.

(* Terms *)

Inductive tm : Set :=
  | TM_Unit
  | TM_Num   : num -> tm
  | TM_Loc   : typ -> num -> tm
  | TM_New   : typ -> tm  -> tm
  | TM_Load  : tm  -> tm
  | TM_Asg   : tm  -> tm  -> tm
  | TM_Id    : id  -> tm
  | TM_Fun   : id  -> typ -> tm -> tm
  | TM_Call  : tm  -> tm  -> tm
  | TM_Seq   : tm  -> tm  -> tm
  | TM_Spawn : tm  -> tm
  .

Theorem tm_eq_dec : forall (t1 t2 : tm),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros. decide equality; 
  eauto using PeanoNat.Nat.eq_dec, Strings.String.string_dec, typ_eq_dec.
Qed.

(* Values *)

Inductive value : tm -> Prop :=
  | V_Unit : value TM_Unit
  | V_Num : forall n, value (TM_Num n)
  | V_Loc : forall ad T, value (TM_Loc ad T)
  | V_Fun : forall x Tx t, value (TM_Fun x Tx t)
  .

(* Effects *)

Definition addr := nat.

Inductive effect : Set :=
  | EF_None
  | EF_Alloc (ad : addr) (t : tm)
  | EF_Load  (ad : addr) (t : tm)
  | EF_Store (ad : addr) (t : tm)
  | EF_Spawn (t : tm)
  .

Theorem effect_eq_dec : forall (e1 e2 : effect),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros. decide equality; eauto using PeanoNat.Nat.eq_dec, tm_eq_dec.
Qed.

(* Substitution *)

Local Infix "=?" := String.string_dec (at level 70, no associativity).

Fixpoint subst (id : id) (x t : tm) : tm :=
  match t with
  | TM_Unit          => t
  | TM_Num _         => t
  | TM_Loc _ _       => t
  | TM_New T t'      => TM_New T ([id := x] t')
  | TM_Load t'       => TM_Load  ([id := x] t')
  | TM_Asg t1 t2     => TM_Asg   ([id := x] t1) ([id := x] t2)
  | TM_Id id'        => if id =? id' then x else t
  | TM_Fun id' Tx t' => if id =? id' then t else TM_Fun id' Tx ([id := x] t')
  | TM_Call t1 t2    => TM_Call  ([id := x] t1) ([id := x] t2)
  | TM_Seq t1 t2     => TM_Seq   ([id := x] t1) ([id := x] t2)
  | TM_Spawn t'      => TM_Spawn ([id := x] t')
  end
  where "'[' id ':=' x ']' t" := (subst id x t).

(* Operational Semantics *)

Inductive step : tm -> effect -> tm -> Prop :=
  (* New *)
  | ST_New1 : forall T t t' eff,
    t --[eff]--> t' ->
    TM_New T t --[eff]--> TM_New T t'

  | ST_New : forall T ad v,
    value v ->
    TM_New T v --[EF_Alloc ad v]--> TM_Loc T ad

  (* Load *)
  | ST_Load1 : forall t t' eff,
    t --[eff]--> t' ->
    TM_Load t --[eff]--> TM_Load t'

  | ST_LoadM : forall ad t T,
    TM_Load (TM_Loc T ad) --[EF_Load ad t]--> t

  (* Asg *)
  | ST_Asg1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    TM_Asg t1 t2 --[eff]--> TM_Asg t1' t2

  | ST_Asg2 : forall v t t' eff,
    value v ->
    t --[eff]--> t' ->
    TM_Asg v t --[eff]--> TM_Asg v t'

  | ST_Asg : forall ad v T,
    value v ->
    TM_Asg (TM_Loc T ad) v --[EF_Store ad v]--> TM_Unit

  (* Call *)
  | ST_Call1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    TM_Call t1 t2 --[eff]--> TM_Call t1' t2

  | ST_Call2 : forall v t t' eff,
    value v ->
    t --[eff]--> t' ->
    TM_Call v t --[eff]--> TM_Call v t'

  | ST_Call : forall x Tx t v,
    value v ->
    TM_Call (TM_Fun x Tx t) v --[EF_None]--> [x := v] t

  (* Seq *)
  | ST_Seq1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    TM_Seq t1 t2 --[eff]--> TM_Seq t1' t2

  | ST_Seq : forall v t,
    value v ->
    TM_Seq v t --[EF_None]--> t

  (* Spawn *)
  | ST_Spawn : forall t,
    TM_Spawn t --[EF_Spawn t]--> TM_Unit

  where "t '--[' eff ']-->' t'" := (step t eff t').

Ltac induction_step :=
  match goal with
  | H : _ --[?e]--> _ |- _ =>
    remember e as eff; induction H; inversion Heqeff; subst
  end.

Ltac inversion_step :=
  match goal with
    | H : _ --[_]--> _ |- _ => inversion H; subst; clear H
  end.

(* Memory Step *)

Definition mem := list tm.
Definition getTM := get TM_Unit.

Inductive mstep : mem -> tm -> effect -> mem -> tm -> Prop :=
  | MST_None : forall m t t',
    t --[EF_None]--> t' ->
    m / t ==[EF_None]==> m / t'

  | MST_Alloc : forall m t t' ad v,
    ad = length m ->
    t --[EF_Alloc ad v]--> t' ->
    m / t ==[EF_Alloc ad v]==> (add m v) / t'

  | MST_Load : forall m t t' ad,
    ad < length m ->
    t --[EF_Load ad (getTM m ad)]--> t' ->
    m / t ==[EF_Load ad (getTM m ad) ]==> m / t'

  | MST_Store : forall m t t' ad v,
    ad < length m ->
    t --[EF_Store ad v]--> t' ->
    m / t ==[EF_Store ad v]==> (set m ad v) / t'

  where "m / t '==[' eff ']==>' m' / t'" := (mstep m t eff m' t').

Ltac inversion_mstep_noclear :=
  match goal with
    | H : _ / _ ==[_]==> _ / _ |- _ => inversion H; subst
  end.

Ltac inversion_mstep :=
  match goal with
    | H : _ / _ ==[_]==> _ / _ |- _ => inversion H; subst; clear H
  end.

(* Concurrent Step *)

Definition threads := list tm.

Inductive cstep : mem -> threads -> nat -> effect -> mem -> threads -> Prop :=
  | CST_Mem : forall m m' t' ths tid eff,
      tid < length ths ->
      m / (getTM ths tid) ==[eff]==> m' / t' ->
      m / ths ~~[tid, eff]~~> m' / (set ths tid t')

  | CST_Spawn : forall m t' ths tid block,
      tid < length ths ->
      (getTM ths tid) --[EF_Spawn block]--> t' ->
      m / ths ~~[tid, EF_Spawn block]~~> m / (add (set ths tid t') block)

  where "m / ths '~~[' tid ,  eff ']~~>' m' / ths'" :=
    (cstep m ths tid eff m' ths').

Ltac inversion_cstep :=
  match goal with
    | H : _ / _ ~~[_, _]~~> _ / _ |- _ => inversion H; subst; clear H
  end.

(* Array Properties *)

Definition memory_property P (m : mem) : Prop :=
  property TM_Unit P m.

Definition threads_property P (ths : threads) : Prop :=
  property TM_Unit P ths.

(* Typing *)

Definition ctx := map typ.
Definition getTY := get TY_Unit.

Inductive well_typed_term : ctx -> tm -> typ -> Prop :=
  | T_Unit : forall Gamma,
    Gamma |-- TM_Unit is TY_Unit

  | T_Num : forall Gamma n,
    Gamma |-- (TM_Num n) is TY_Num

  | T_Loc : forall Gamma ad T,
    Gamma |-- (TM_Loc T ad) is T

  | T_NewM : forall Gamma t T,
    Gamma |-- t is T ->
    Gamma |-- (TM_New (TY_RefM T) t) is (TY_RefM T)

  | T_NewI : forall Gamma t T,
    Gamma |-- t is T ->
    Gamma |-- (TM_New (TY_RefI T) t) is (TY_RefI T)

  | T_LoadM : forall Gamma t T,
    Gamma |-- t is TY_RefM T ->
    Gamma |-- (TM_Load t) is T

  | T_LoadI : forall Gamma t T,
    Gamma |-- t is TY_RefI T ->
    Gamma |-- (TM_Load t) is T

  | T_Asg : forall Gamma t1 t2 T,
    Gamma |-- t1 is (TY_RefM T) ->
    Gamma |-- t2 is T ->
    Gamma |-- (TM_Asg t1 t2) is TY_Unit

  | T_Fun : forall Gamma x t T Tx,
    (update Gamma x Tx) |-- t is T ->
    Gamma |-- (TM_Fun x Tx t) is (TY_Fun Tx T)

  | T_Call : forall Gamma t1 t2 T Tx,
    Gamma |-- t1 is (TY_Fun Tx T) ->
    Gamma |-- t2 is Tx ->
    Gamma |-- (TM_Call t1 t2) is T

  | T_Seq : forall Gamma t1 t2 T1 T2,
    Gamma |-- t1 is T1 ->
    Gamma |-- t2 is T2 ->
    Gamma |-- (TM_Seq t1 t2) is T2

  | T_Spawn : forall Gamma t T,
    empty |-- t is T ->
    Gamma |-- (TM_Spawn t) is TY_Unit

  where "Gamma '|--' t 'is' T" := (well_typed_term Gamma t T).

Ltac induction_type :=
  match goal with
  | H : _ |-- _ is _ |- _ =>
    induction H
  end.

Ltac inversion_type :=
  match goal with
  | H : _ |-- _ is _ |- _ =>
    inversion H; subst; clear H
  end.
