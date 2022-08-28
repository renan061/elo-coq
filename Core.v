From Coq Require Import Strings.String.
From Coq Require Import List.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
 
Definition id := string.
Definition num := nat.

(* Notations *)

Reserved Notation "'[' x ':=' tx ']' t"
  (at level 20, x constr).
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

Declare Custom Entry elo_typ.
Notation "<{{ T }}>" := T (T custom elo_typ at level 99).
Notation "( x )"     := x (in custom elo_typ, x at level 99).
Notation "x"         := x (in custom elo_typ at level 0, x constr at level 0).

Notation "'Unit'"   := (TY_Unit)      (in custom elo_typ at level 0).
Notation "'Num'"    := (TY_Num)       (in custom elo_typ at level 0).
Notation "'&m' T"   := (TY_RefM T)    (in custom elo_typ at level 5).
Notation "'&i' T"   := (TY_RefI T)    (in custom elo_typ at level 5).
Notation "T1 -> T2" := (TY_Fun T1 T2) (in custom elo_typ at level 50,
                                                right associativity).

Theorem typ_eq_dec : forall (t1 t2 : typ),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros. decide equality; eauto.
Qed.

(* Terms *)

Inductive tm : Set :=
  | TM_Unit
  | TM_Num   : num -> tm
  | TM_Ref   : typ -> num -> tm
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
  eauto using PeanoNat.Nat.eq_dec, string_dec, typ_eq_dec.
Qed.

(* Syntax *)

(* Declare Custom Entry stlc_ty. *)

Declare Custom Entry elo.
Notation "<{ t }>" := t (t custom elo at level 99).
Notation "( x )"   := x (in custom elo, x at level 99).
Notation "x"       := x (in custom elo at level 0, x constr at level 0).

Notation "'unit'"                 := (TM_Unit)       (in custom elo at level 0).
Notation "'N' n"                  := (TM_Num n)      (in custom elo at level 0,
                                                                  n at level 0).
Notation "'&' ad ':' T"           := (TM_Ref T ad)   (in custom elo at level 0,
                                                   T custom elo_typ at level 0,
                                                                 ad at level 0).
Notation "'new' T t"              := (TM_New T t)    (in custom elo at level 0,
                                                   T custom elo_typ at level 0,
                                                       t custom elo at level 0).
Notation "'*' t"                  := (TM_Load t)     (in custom elo at level 0,
                                                       t custom elo at level 0).
Notation "t1 '=' t2"              := (TM_Asg t1 t2)  (in custom elo at level 1,
                                                            left associativity).
Notation "'ID' x"                 := (TM_Id x)       (in custom elo at level 0,
                                                                  x at level 0).
Notation "'fun' x ':' Tx '->' t"  := (TM_Fun x Tx t) (in custom elo at level 0,
                                                                  x at level 0,
                                                  Tx custom elo_typ at level 0,
                                                       t custom elo at level 0).
Notation "t1 t2"                  := (TM_Call t1 t2) (in custom elo at level 1,
                                                            left associativity).
Notation "t1 ';' t2"              := (TM_Seq t1 t2)  (in custom elo at level 1,
                                                            left associativity).
Notation "'spawn' t"              := (TM_Spawn t)    (in custom elo at level 0,
                                                                  t at level 0).

(* Values *)

Inductive value : tm -> Prop :=
  | V_Unit : value <{ unit }> 
  | V_Num : forall n, value <{ N n }>
  | V_Ref : forall ad T, value <{ &ad: T }>
  | V_Fun : forall x Tx t, value <{ fun x: Tx -> t }>
  .

(* Effects *)

Definition addr := nat.

Inductive effect : Set :=
  | EF_None
  | EF_Alloc (ad : addr) (t : tm)
  | EF_Read  (ad : addr) (t : tm)
  | EF_Write (ad : addr) (t : tm)
  | EF_Spawn (t : tm)
  .

Theorem effect_eq_dec : forall (e1 e2 : effect),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros. decide equality; eauto using PeanoNat.Nat.eq_dec, tm_eq_dec.
Qed.

(* Substitution *)

Local Infix "=?" := string_dec (at level 70, no associativity).

Fixpoint subst (x : id) (tx t : tm) : tm :=
  match t with
  | <{ unit }>             => t
  | <{ N _ }>              => t
  | <{ & _ : _ }>          => t
  | <{ new T t' }>         => TM_New T ([x := tx] t')
  | <{ *t' }>              => TM_Load  ([x := tx] t')
  | <{ t1 = t2 }>          => TM_Asg   ([x := tx] t1) ([x := tx] t2)
  | <{ ID x' }>            => if x =? x' then tx else t
  | <{ fun x': Tx -> t' }> => if x =? x'
                                then t 
                                else TM_Fun x' Tx ([x := tx] t')
  | <{ t1 t2  }>           => TM_Call  ([x := tx] t1) ([x := tx] t2)
  | <{ t1; t2 }>           => TM_Seq   ([x := tx] t1) ([x := tx] t2)
  (* | <{ spawn t' }>         => TM_Spawn ([x := tx] t') *)
  | <{ spawn t' }>         => t
  end
  where "'[' id ':=' x ']' t" := (subst id x t).

(* Operational Semantics *)

Inductive step : tm -> effect -> tm -> Prop :=
  (* New *)
  | ST_New1 : forall T t t' eff,
    t --[eff]--> t' ->
    <{ new T t }> --[eff]--> <{ new T t' }>

  | ST_New : forall T ad v,
    value v ->
    <{ new T v }> --[EF_Alloc ad v]--> <{ &ad: T }>

  (* Load *)
  | ST_Load1 : forall t t' eff,
    t --[eff]--> t' ->
    <{ *t }> --[eff]--> <{ *t' }>

  | ST_LoadM : forall ad t T,
    <{ * (&ad: T) }> --[EF_Read ad t]--> t

  (* Asg *)
  | ST_Asg1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    <{ t1 = t2 }> --[eff]--> <{ t1' = t2 }>

  | ST_Asg2 : forall v t t' eff,
    value v ->
    t --[eff]--> t' ->
    <{ v = t }> --[eff]--> <{ v = t' }>

  | ST_Asg : forall ad v T,
    value v ->
    <{ &ad: T = v }> --[EF_Write ad v]--> <{ unit }> 

  (* Call *)
  | ST_Call1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    <{ t1 t2 }> --[eff]--> <{ t1' t2 }>

  | ST_Call2 : forall v t t' eff,
    value v ->
    t --[eff]--> t' ->
    <{ v t }> --[eff]--> <{ v t' }>

  | ST_Call : forall x Tx t v,
    value v ->
    <{ (fun x: Tx -> t) v }> --[EF_None]--> [x := v] t

  (* Seq *)
  | ST_Seq1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    <{ t1; t2 }> --[eff]--> <{ t1'; t2 }>

  | ST_Seq : forall v t,
    value v ->
    <{ v; t }> --[EF_None]--> t

  (* Spawn *)
  | ST_Spawn : forall t,
    <{ spawn t }> --[EF_Spawn t]--> <{ unit }>

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

  | MST_Read : forall m t t' ad,
    ad < length m ->
    t --[EF_Read ad (getTM m ad)]--> t' ->
    m / t ==[EF_Read ad (getTM m ad)]==> m / t'

  | MST_Write : forall m t t' ad v,
    ad < length m ->
    t --[EF_Write ad v]--> t' ->
    m / t ==[EF_Write ad v]==> (set m ad v) / t'

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
    Gamma |-- <{ unit }> is <{{ Unit }}>

  | T_Num : forall Gamma n,
    Gamma |-- <{ N n }> is <{{ Num }}>

  | T_Ref : forall Gamma ad T,
    Gamma |-- <{ &ad: T }> is T

  | T_NewM : forall Gamma t T,
    Gamma |-- t is T ->
    Gamma |-- <{ new (&m T) t }> is <{{ &m T }}>

  | T_NewI : forall Gamma t T,
    Gamma |-- t is T ->
    Gamma |-- <{ new (&i T) t }> is <{{ &i T }}>

  | T_LoadM : forall Gamma t T,
    Gamma |-- t is <{{ &m T }}> ->
    Gamma |-- <{ *t }> is T

  | T_LoadI : forall Gamma t T,
    Gamma |-- t is <{{ &i T }}> ->
    Gamma |-- <{ *t }> is T

  | T_Asg : forall Gamma t1 t2 T,
    Gamma |-- t1 is <{{ &m T }}> ->
    Gamma |-- t2 is T ->
    Gamma |-- <{ t1 = t2 }> is <{{ Unit }}>

  | T_Fun : forall Gamma x t T Tx,
    Gamma[x <== Tx] |-- t is T ->
    Gamma |-- <{ fun x: Tx -> t }> is <{{ Tx -> T }}>

  | T_Call : forall Gamma t1 t2 T Tx,
    Gamma |-- t1 is <{{ Tx -> T }}> ->
    Gamma |-- t2 is Tx ->
    Gamma |-- <{ t1 t2 }> is T

  | T_Seq : forall Gamma t1 t2 T1 T2,
    Gamma |-- t1 is T1 ->
    Gamma |-- t2 is T2 ->
    Gamma |-- <{ t1; t2 }> is T2

  | T_Spawn : forall Gamma t T,
    empty |-- t is T ->
    Gamma |-- <{ spawn t }> is <{{ Unit }}> 

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

