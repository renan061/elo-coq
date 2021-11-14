From Coq Require Import Init.Nat.

From Elo Require Export Core.

Definition synchronize (threads : list tm) (i j : nat) : Prop := False.

Definition happens_before (threads : list tm) i j : Prop :=
  if i =? j then i < j else synchronize threads i j.

Definition is_write (t : tm) : Prop := 
  match t with
  | TM_Asg _ _ | TM_ArrAsg _ _ _ => True
  | _ => False
  end.

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