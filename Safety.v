From Coq Require Import Init.Nat.

From Elo Require Export Array.
From Elo Require Export Map.

From Elo Require Export Core.
From Elo Require Export Properties.

Reserved Notation "m / ths '==[' f ']==>+' m' / ths'"
  (at level 40, ths at next level, f at next level, m' at next level).

Inductive multistep (f : ceffect -> Prop) :
  mem -> list tm -> mem -> list tm -> Prop :=

  | multistep_first : forall m m' ths ths' ceff,
    f ceff ->
    m / ths ==> m' / ths' # ceff ->
    m / ths ==[f]==>+ m' / ths'

  | multistep_step : forall m1 m m2 ths1 ths ths2 ceff,
    f ceff ->
    m1 / ths1 ==> m / ths # ceff ->
    m  / ths  ==[f]==>+ m2 / ths2 ->
    m1 / ths1 ==[f]==>+ m2 / ths2

  where "m / ths '==[' f ']==>+' m' / ths'" := (multistep f m ths m' ths').

Reserved Notation "m / ths '==[' f ']==>+' m' / ths'"
  (at level 40, ths at next level, f at next level, m' at next level).

Inductive sequence : list ceffect -> mem -> list tm -> Prop :=
  | sequence_nil : forall main,
    sequence (CEF_None 0 :: nil) nil (main :: nil)

  | sequence_cons : forall m m' ths ths' ceff ceffs,
    m / ths ==> m' / ths' # ceff ->
    sequence ceffs  m  ths ->
    sequence (ceff :: ceffs) m' ths'
  .

Definition is_same_thread ceff i :=
  match ceff with
  | CEF_None  j
  | CEF_Alloc j _
  | CEF_Load  j _
  | CEF_Store j _
  | CEF_Spawn j   => i =? j
  end.

Definition is_write ceff addr :=
  match ceff with
  | CEF_Store _ addr' => addr =? addr'
  | _ => false
  end.

Definition is_not_concurrent_write (i addr : nat) (ceff : ceffect) :=
  False.

Theorem aux : forall m1 m2 m3 ths1 ths2 ths3 i addr,
  m1 / ths1 ==> m2 / ths2 # (CEF_Load i addr) ->
  m2 / ths2 ==[is_not_concurrent_write i addr]==>+ m3 / ths3.
Proof.
Admitted.



Inductive before : list tm -> list tm -> Prop :=
  | todo : forall i j eff eff' m m' ths ths',
    i < j ->
    sequence i eff  m  ths  ->
    sequence j eff' m' ths' ->
    before ths ths'
  .

Definition synchronize (threads : list tm) (i j : nat) : Prop := False.

Definition happens_before (threads : list tm) i j : Prop :=
  if i =? j then i < j else synchronize threads i j.

Definition data_race := forall (threads : list tm) i j,
  (is_write (get_tm threads i) \/ is_write (get_tm threads j)) /\
  ~ happens_before threads i j.

(*
Inductive happens_before' : mem -> tm -> mem -> tm -> Prop :=
  | HB_Step : forall m m' t t',
    m / t -->* m' / t' ->
    happens_before' m t m' t'
  .
*)

(*
  Invariant:
    At any time during program execution, each thread or monitor can only
    access memory locations that are either local or safe.
*)