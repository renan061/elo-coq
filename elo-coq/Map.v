From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Elo Require Export Array.

Local Definition map' (A : Type) := string -> A. (* total map *)

Local Definition empty' {A : Type} v : map' A := (fun _ => v).

Local Definition update' {A : Type} (m : map' A) k v :=
  fun k' => if String.eqb k k' then v else m k'.

Definition map (A : Type) := map' (option A). (* partial map *)

Definition empty {A : Type} : map A := empty' None.

Definition update {A : Type} (m : map A) k v :=
  update' m k (Some v).

Definition lookup {A : Type} (m : map A) k := m k.



(* Definition map A := list (string * A).

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
  end. *)