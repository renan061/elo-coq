From Coq Require Import Lists.List.

Local Definition map' (K V : Type) :=
  prod (K -> V) (K -> K -> bool).

Local Definition empty' {K V : Type} v eqb : map' K V := (fun _ => v, eqb).

Local Definition update' {K V : Type} (m : map' K V) k v :=
  (fun k' => if (snd m) k k' then v else (fst m) k', snd m).

Local Definition map (K V : Type) := map' K (option V).

Local Definition empty {K V : Type} eqb : map K V := empty' None eqb.

Local Definition update {K V : Type} (m : map K V) k v :=
  update' m k (Some v).

Local Definition lookup {K V : Type} (m : map K V) k := (fst m) k.

Definition multimap (K V : Type) := map' K (list V).

Definition multimap_empty {K V : Type} eqb : multimap K V :=
  empty' nil eqb.

Definition multimap_lookup {K V : Type} (m : multimap K V) k : list V :=
  fst m k.

Definition multimap_contains {K V : Type} (m : multimap K V) k v : Prop :=
  In v (multimap_lookup m k).

Definition multimap_update {K V : Type} (m : multimap K V) k v :=
  update' m k (v :: multimap_lookup m k).
