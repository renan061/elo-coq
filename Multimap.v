
Local Definition map' (K V : Type) :=
  prod (K -> V) (K -> K -> bool).

Local Definition empty' {K V : Type} v eqb : map' K V := (fun _ => v, eqb).

Local Definition update' {K V : Type} (m : map' K V) k v :=
  (fun k' => if (snd m) k k' then v else (fst m) k', snd m).


Definition map (K V : Type) := map' K (option V).

Definition empty {K V : Type} eqb : map K V := empty' None eqb.

Definition update {K V : Type} (m : map K V) k v :=
  update' m k (Some v).

Definition lookup {K V : Type} (m : map K V) k := (fst m) k.


Definition multimap (K V : Type) := map K (map' V V).

(*
Definition multimap_empty {K V : Type} eqbk eqbv :=
  empty' (empty  V) nil eqb.
*)