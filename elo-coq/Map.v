From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Elo Require Export Array.

(* Inductive list2 {A B: Type} : Type :=
  | nil2
  | cons2 (a : A) (b : B) (m : list2).

Definition map A := @list2 string A.

Local Fixpoint index_of' {A} (m : map A) (k : string) (i : nat) :=
  match m with
  | nil2 => None
  | cons2 k' v' m' => if eqb k k'
    then Some (i, v')
    else index_of' m' k (i + 1)
  end.

Definition index_of {A} m k := @index_of' A m k 0.

Definition update {A} (m : map A) k v :=
  match index_of m k with
  | None => m ++ (cons2 k v nil2)
  | Some (i, _) => nil2
  end.

Definition lookup {A} (m : map A) k :=
  match index_of m k with
  | None => None
  | Some (_, v) => Some v
  end.
*)

Definition map A := list (string * A).

Local Fixpoint index_of' {A} (m : map A) (k : string) (i : nat) :=
  match m with
  | nil => None
  | (k', v) :: m' => if eqb k k'
    then Some (i, v)
    else index_of' m' k (i + 1)
  end.

Definition index_of {A} m k := @index_of' A m k 0.

Definition update {A} (m : map A) k v :=
  match index_of m k with
  | None => add m (k, v)
  | Some (i, _) => set m i (k, v)
  end.

Definition lookup {A} (m : map A) k :=
  match index_of m k with
  | None => None
  | Some (_, v) => Some v
  end.