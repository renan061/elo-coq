From Coq Require Init.Nat.
From Coq Require Strings.String.

From Coq Require Import Lists.List.

Module Map.
  Local Definition map' (A B : Type) := A -> B. (* total map *)

  Local Definition empty' {A B : Type} v : map' A B := (fun _ => v).

  Local Definition update' {A B : Type} (m : map' A B) k v (eq : A -> A -> bool) :=
    fun k' => if eq k k' then v else m k'.

  Definition map (A B : Type) := map' A (option B). (* partial map *)

  Definition empty {A B : Type} : map A B := empty' None.

  Definition update {A B : Type} (m : map A B) k v (eq : A -> A -> bool) :=
    update' m k (Some v) eq.
End Map.

Import Map.

Definition M (A : Type) := prod (prod (map String.string A) (map nat A)) nat.

Definition lookup_names {A} (m : M A) := fst (fst m).

Definition lookup_locs {A} (m : M A) := snd (fst m).

Definition allocate {A} (m : M A) a : M A :=
  let (maps, n) := m in
  let (names, locs) := maps in
  let i := n + 1 in
  (names, update locs i a Nat.eqb, i)
.

Definition allocate_val {A} (m : M A) name a : M A :=
  let (maps, n) := m in
  let (names, locs) := maps in
  (update names name a String.eqb, locs, n)
.

Definition allocate_var {A} (m : M A) name (f : nat -> A) a : M A :=
  let (maps, n) := allocate m a in
  let (names, locs) := maps in
  (update names name (f n) String.eqb, locs, n)
.

Definition assign {A} (m : M A) i a : M A :=
  let (maps, n) := allocate m a in
  let (names, locs) := maps in
  (names, update locs i a Nat.eqb, n + 1)
.

Definition name := String.string.
Definition num := nat.

(* ******************************************************************************** *)

(* Types *)

Inductive typ : Set :=
  | TY_Void
  | TY_Num
  | TY_Array : typ -> typ
  | TY_ImmutArray : typ -> typ
  | TY_Ref : typ -> typ
  | TY_ImmutRef : typ -> typ
  .

(* Terms *)

Inductive tm : Set :=
  | TM_Nil
  | TM_Num : num -> tm
  | TM_Array : tm -> tm
  | TM_ImmutArray : tm -> tm
  | TM_Variable : name -> tm
  | TM_Indexation : tm' -> tm -> tm
  | TM_Call : name -> tm -> tm
  | TM_LetVal : name -> tm -> tm -> tm
  | TM_LetVar : name -> tm -> tm -> tm
  | TM_Asg : tm' -> tm -> tm
  | TM_Seq : tm -> tm -> tm

with tm' : Set :=
  | TM : tm -> tm'
  | TM_Ref (_ : num)
  .

Coercion TM : tm >-> tm'.

Inductive global : Set :=
  | TM_GlobalVal (_ : name) (_ : tm)
  | TM_Function (f : name) (pn : name) (pt : typ) (block : tm) (re : tm) (rt : typ)
  .

Definition program := list global.

(* Values *)

Inductive value : tm' -> Prop :=
  | V_Nil :
    value TM_Nil

  | V_Num : forall n,
    value (TM_Num n)

  | V_Ref : forall i,
    value (TM_Ref i)
  .

(* Typing *)

Definition context := map name typ.
Definition mem_ty := list typ.

Definition get {A} (l : list A) (i : nat) := nth_error l i.

Fixpoint set {A} (l : list A) (i : nat) (a : A) : list A :=
  match l with
  | nil => nil
  | x :: xs =>
    match i with
    | O => a :: xs
    | S i' => x :: set xs i' a
    end
  end.

Definition add {A} (l : list A) (a : A) := l ++ (a :: nil).

Reserved Notation "Gamma '/' MT '|-' tm 'is' T" (at level 40, T at level 0).

Inductive typeof : context -> mem_ty -> tm' -> typ -> Prop :=
  | T_Nil : forall Gamma MT,
    Gamma / MT |- TM_Nil is TY_Void

  | T_Num : forall Gamma MT n,
    Gamma / MT |- (TM_Num n) is TY_Num
(*
  | T_Array : forall Gamma MT (t : tm) (A : typ),
    let MT' := add MT A in
    Gamma / MT |- t is A ->
    Gamma / MT' |- (TM_Array t) is (TY_Array A)

  | T_ImmutArrayNum : forall Gamma (t : tm),
    let T := TY_Num in
    let Gamma' := @allocate typ' Gamma T in
    Gamma / MT |- t is T ->
    Gamma' / MT |- (TM_ImmutArray t) is (TY_ImmutArray T)

  | T_ImmutArrayImmutArray : forall Gamma (t : tm) A,
    let T := TY_ImmutArray A in
    let Gamma' := @allocate typ' Gamma T in
    Gamma / MT |- t is T ->
    Gamma' / MT |- (TM_ImmutArray t) is (TY_ImmutArray T)
*)
  | T_VariableVal : forall Gamma MT name A B,
    A <> TY_Ref B -> (* TODO what about arrays? *)
    Gamma name = Some A ->
    Gamma / MT |- (TM_Variable name) is A

  | T_VariableVar : forall Gamma MT name A,
    Gamma name = Some (TY_Ref A) ->
    Gamma / MT |- (TM_Variable name) is A
(*
  | T_Indexation1 : forall Gamma (arr i : tm) A,
    Gamma / MT |- arr is (TY_Array A) ->
    Gamma / MT |- i is TY_Num ->
    Gamma / MT |- (TM_Indexation arr i) is A

  | T_Indexation2 : forall Gamma (arr i : tm) A,
    Gamma / MT |- arr is (TY_ImmutArray A) ->
    Gamma / MT |- i is TY_Num ->
    Gamma / MT |- (TM_Indexation arr i) is A
    (*
      | ST_Indexation : forall m i e,
    lookup_locs m i = Some e ->
    m / TM_Indexation (TM_Ref i) (TM_Num 0) --> m / e
*)
  | T_Call : forall Gamma f (p : tm) A B,
    lookup_names Gamma f = Some (TY_Function A B) ->
    Gamma / MT |- p is A ->
    Gamma / MT |- (TM_Call f p) is B

  | T_LetVal : forall Gamma name (e t : tm) A B,
    let Gamma' := allocate_val Gamma name A in
    Gamma / MT |- e is A ->
    Gamma' / MT |- t is B ->
    Gamma / MT |- (TM_LetVal name e t) is B

  | T_LetVar : forall Gamma name (e t : tm) A B,
    let Gamma' := allocate_var Gamma name (fun _ => TY_Ref A) A in
    Gamma / MT |- e is A ->
    Gamma' / MT |- t is B ->
    Gamma / MT |- (TM_LetVal name e t) is B

  | T_Asg : forall Gamma i (t : tm) A,
    lookup_locs Gamma i = Some A ->
    Gamma / MT |- t is A ->
    Gamma / MT |- (TM_Asg (TM_Ref i) t) is TY_Void

  | T_Seq : forall Gamma (t1 t2 : tm) A,
    Gamma / MT |- t1 is TY_Void ->
    Gamma / MT |- t2 is A ->
    Gamma / MT |- (TM_Seq t1 t2) is A
*)

  | T_Ref : forall Gamma MT i A,
    i < length MT ->
    get MT i = Some A ->
    Gamma / MT |- (TM_Ref i) is (TY_Ref A)

  where "Gamma '/' MT '|-' tm 'is' T" := (typeof Gamma MT tm T).

Theorem unique_types : forall Gamma t A B,
  Gamma / MT |- t is A -> Gamma / MT |- t is B -> A = B.
Proof.
  intros Gamma t A B HA.
  generalize dependent B.
  induction HA; intros B' HB; inversion HB; subst; try congruence;
  try (f_equal; eauto).
  Admitted.

(* Operational Semantics *)

Definition memory := M tm'.

Reserved Notation "a '/' b '-->' c '/' d" (at level 40, b at level 39, c at level 39).

(*
Tentar fazer
Inductive step_exp {p : P}
onde p é o mapeamento para as funções
*)
Inductive step : memory -> tm' -> memory -> tm' -> Prop :=
  | ST_Array1: forall m m' (e e' : tm),
    m / e --> m' / e' -> 
    m / TM_Array e --> m' / TM_Array e'

  | ST_Array: forall m (e : tm),
    let m' := @allocate tm' m e in
    value e ->
    m / TM_Array e --> m' / TM_Ref (snd m')

  | ST_ImmutArray1: forall m m' (e e' : tm),
    m / e --> m' / e' -> 
    m / TM_ImmutArray e --> m' / TM_ImmutArray e'

  | ST_ImmutArray: forall m (e : tm),
    let m' := @allocate tm' m e in
    value e ->
    m / TM_ImmutArray e --> m' / TM_Ref (snd m')

  | ST_Variable : forall m name e,
    lookup_names m name = Some e ->
    m / TM_Variable name --> m / e

  | ST_Indexation1 : forall m m' (arr arr' : tm) i,
    m / arr --> m' / arr' ->
    m / TM_Indexation arr i --> m' / TM_Indexation arr' i

  | ST_Indexation2 : forall m m' (arr i i' : tm),
    value arr ->
    m / i --> m' / i' ->
    m / TM_Indexation arr i --> m' / TM_Indexation arr i'

  | ST_Indexation : forall m i e,
    lookup_locs m i = Some e ->
    m / TM_Indexation (TM_Ref i) (TM_Num 0) --> m / e

(*
  | ST_Call1 : forall m m' e e' name,
    (m, e) --e--> (m', e') -> 
    (m, TM_Call name e) --e--> (m', TM_Call name e')

  | ST_Call : forall m m' e name param,
    value param ->
    (* TODO
    // lookup function by name and eval it to get 'e'
    // precisa de contexto em separado para definições de funções?
    step_stat m stats m' stats' ->
    step_global m (TM_Function a b c stats d) m' (TM_Function a b c stats' d)
    *)
    (m, TM_Call name param) --e--> (m', e)
*)

  | ST_LetVal1 : forall m m' name (e e': tm) t,
    m / e --> m' / e' ->
    m / TM_LetVal name e t --> m' / TM_LetVal name e' t

  | ST_LetVal : forall m name (e : tm) t,
    value e ->
    m / TM_LetVal name e t --> (@allocate_val tm' m name e) / t

  | ST_LetVar1 : forall m m' name (e e': tm) t,
    m / e --> m' / e' ->
    m / TM_LetVar name e t --> m' / TM_LetVar name e' t

  | ST_LetVar : forall m name (e : tm) t,
    value e ->
    m / TM_LetVar name e t --> (@allocate_var tm' m name TM_Ref e) / t

  | ST_Asg1 : forall m m' t (e e' : tm),
    m / e --> m' / e' ->
    m / TM_Asg t e --> m' / TM_Asg t e'

  | ST_Asg2 : forall m m' (t t' e : tm),
    value e ->
    m / t --> m' / t' ->
    m / TM_Asg t e --> m' / TM_Asg t' e

  | ST_Asg : forall m (e : tm) i,
    value e ->
    m / TM_Asg (TM_Ref i) e --> assign m i e / TM_Nil

  | ST_Seq1 : forall m m' (t1 t2 : tm) t,
    m / t1 --> m' / t2 -> 
    m / TM_Seq t1 t --> m' / TM_Seq t2 t

  | ST_Seq : forall m t,
    m / TM_Seq TM_Nil t --> m / t

  where "a '/' b '-->' c '/' d" := (step a b c d).

(*
Inductive step_program : memory -> program -> memory -> program -> Prop :=
  | ST_GlobalVal1 : forall m m' s s' program name e,
    s = TM_ValDef name e -> (* TODO like this? *)
    (m, s) --s--> (m', s') ->
    step_program m (TM_GlobalVal s :: program) m' (TM_GlobalVal s' :: program)

  | ST_GlobalVal2 : forall m program,
    step_program m (TM_GlobalVal TM_Skip :: program) m program

  (*
  | ST_Function : forall m m' program f pn pt s r,
    m' = update m f (V_Function pn pt s r) ->
    step_program m (TM_Function f pn pt s r :: program) m' program

  | ST_Run : forall m program
    program = [] ->
    m "main" = TM_Function "main" "" stats TY_Void ->
    call main!
    step_exp m (TM_Call "main" TM_Nil) m' ret ->
    value ret = value TM_Nil
  *)
.

*)

(* ******************************************************************************** *)
(* ******************************************************************************** *)
(* ******************************************************************************** *)

(*

- Tirei ArrayConstructor => Assim não tem como construir array de tamanho dinâmico,
    mas whatever.
- Tirei cast, pq whatever. Só existia cast de Int para Float.
- Tirei Call de stat, pq pode por no Asg. Tão expressivo quanto.
- Deixei Ret em asg, por conta do Ret dentro de spawn.
- Mudei array pra só ter um elemento. Pq não sabia fazer a semântica operacional.
- Não tem recursão né? a averiguar!
- | TM_AsgArr (arr : name) (i : exp) (rhs : exp) => array é name!!! coisas como
    [[0]][0][0] = 0; são desnecessárias. Não acredito que perde expressividade. é
    só usar variáveis intermediárias para indexar usando arrays intermediários.

- Em assingments:
  (* TODO is not a val *)
  (* TODO enforce type cannot be TImmutArray? *)
  (* TODO best way to signalize that is a val (cannot be reassigned)? *)
  Esse tipo de coisa só checamos na tipagem! (?)

- How?
  Inductive nope1 : A -> Prop :=
    | nope2: rel 0.

*)













