From Elo Require Import Map.
From Elo Require Import Core.

Definition well_typed_term (t : tm) :=
  exists T, empty |-- t is T.

