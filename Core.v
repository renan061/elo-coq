From Coq Require Import Arith.
From Coq Require Import Strings.String.
From Coq Require Import List.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
 
(* ------------------------------------------------------------------------- *)
(* types                                                                     *)
(* ------------------------------------------------------------------------- *)

(* immutable type *)
Inductive ityp : Set :=
  | TY_Unit
  | TY_Num
  | TY_RefI : ityp -> ityp
  .

(* type *)
Inductive typ : Set :=
  | TY_Immut : ityp -> typ
  | TY_RefM  : typ  -> typ
  | TY_Fun   : typ  -> typ -> typ
  .

(* ------------------------------------------------------------------------- *)
(* terms                                                                     *)
(* ------------------------------------------------------------------------- *)

Definition id := string.
Definition num := nat.

Inductive tm : Set :=
  (* primitives *)
  | TM_Unit
  | TM_Num   : num -> tm
  (* memory *)
  | TM_Ad    : num -> typ -> tm
  | TM_New   : typ -> tm  -> tm
  | TM_Load  : tm  -> tm
  | TM_Asg   : tm  -> tm  -> tm
  (* functions *)
  | TM_Var   : id  -> tm
  | TM_Fun   : id  -> typ -> tm -> tm
  | TM_Call  : tm  -> tm  -> tm
  (* sequencing *)
  | TM_Seq   : tm  -> tm  -> tm
  (* concurrency *)
  | TM_Spawn : tm  -> tm
  .

(* ------------------------------------------------------------------------- *)
(* notations                                                                 *)
(* ------------------------------------------------------------------------- *)

Declare Custom Entry elo_typ.
Notation "<{{ T }}>" := T (T custom elo_typ at level 99).
Notation "( x )"     := x (in custom elo_typ, x at level 99).
Notation "x"         := x (in custom elo_typ at level 0, x constr at level 0).

Notation "'Unit'"      := (TY_Immut TY_Unit)     (in custom elo_typ at level 0).
Notation "'Num'"       := (TY_Immut TY_Num)      (in custom elo_typ at level 0).
Notation "'Immut' T"   := (TY_Immut T)           (in custom elo_typ at level 5).
Notation "'&' T"       := (TY_RefM T)            (in custom elo_typ at level 5).
Notation "'i&' T"      := (TY_Immut (TY_RefI T)) (in custom elo_typ at level 5).
Notation "T1 '-->' T2" := (TY_Fun T1 T2)         (in custom elo_typ at level 50,
                                                           right associativity).

Declare Custom Entry elo_tm.
Notation "<{ t }>" := t (t custom elo_tm at level 99).
Notation "x"       := x (in custom elo_tm at level 0, x constr at level 0).

Notation "'unit'"        := (TM_Unit)       (in custom elo_tm at level 0).
Notation "'N' n"         := (TM_Num n)      (in custom elo_tm at level 0).
Notation "'&' ad '::' T" := (TM_Ad ad T)     (in custom elo_tm at level 0,
                                             T custom elo_typ at level 0).
Notation "'new' T t"     := (TM_New T t)     (in custom elo_tm at level 0,
                                             T custom elo_typ at level 0).
Notation "'*' t"         := (TM_Load t)     (in custom elo_tm at level 0).
Notation "t1 '=' t2"     := (TM_Asg t1 t2)  (in custom elo_tm at level 70,
                                                        no associativity).
Notation "'var' x"       := (TM_Var x)      (in custom elo_tm at level 0).
Notation "'fn' x Tx t"   := (TM_Fun x Tx t)  (in custom elo_tm at level 0,
                                                      x constr at level 0,
                                            Tx custom elo_typ at level 0).
Notation "'call' t1 t2"  := (TM_Call t1 t2) (in custom elo_tm at level 0).
Notation "t1 ';' t2"     := (TM_Seq t1 t2)   (in custom elo_tm at level 2,
                                                     right associativity).
Notation "'spawn' t"     := (TM_Spawn t)    (in custom elo_tm at level 0).

Reserved Notation "'[' x ':=' tx ']' t"
  (at level 20, x constr).
Reserved Notation "t '--[' e ']-->' t'"
  (at level 40, e at next level, t' at next level).
Reserved Notation "m / t '==[' e ']==>' m' / t'"
  (at level 40, t at next level, e at next level, m' at next level).
Reserved Notation "m / ths '~~[' tid , e ']~~>' m' / ths'"
  (at level 40, ths at next level, tid at next level, e at next level,
                m' at next level).
Reserved Notation "m / t '~~[' tc ']~~>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).
Reserved Notation "Gamma '|--' t 'is' T"
  (at level 40).

(* ------------------------------------------------------------------------- *)
(* values                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive value : tm -> Prop :=
  | V_Unit : value <{ unit }> 
  | V_Num : forall n, value <{ N n }>
  | V_Ref : forall ad T, value <{ &ad :: T }>
  | V_Fun : forall x Tx t, value <{ fn x Tx t }>
  .

(* ------------------------------------------------------------------------- *)
(* effects                                                                   *)
(* ------------------------------------------------------------------------- *)

Definition addr := nat.

Inductive effect : Set :=
  | EF_None
  | EF_Alloc (ad : addr) (v : tm) (T : typ)
  | EF_Read  (ad : addr) (v : tm)
  | EF_Write (ad : addr) (v : tm) (T : typ)
  | EF_Spawn (t : tm)
  .

(* ------------------------------------------------------------------------- *)
(* typing                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition ctx := map typ.

(* Filters out of the context all variables with non-immutable types. *)
Definition safe (Gamma : ctx) : ctx :=
  fun k => 
    match Gamma k with
    | Some <{{ Immut T }}> => Some <{{ Immut T }}>
    | _ => None
    end.

Inductive type_of : ctx -> tm -> typ -> Prop :=
  | T_Unit : forall Gamma,
    Gamma |-- <{ unit }> is <{{ Unit }}>

  | T_Num : forall Gamma n,
    Gamma |-- <{ N n }> is <{{ Num }}>

  | T_RefM : forall Gamma ad T,
    Gamma |-- <{ &ad :: &T }> is <{{ &T }}>

  | T_RefI : forall Gamma ad T,
    Gamma |-- <{ &ad :: i&T }> is <{{ i&T }}>

  | T_NewM : forall Gamma t T,
    Gamma |-- t is T ->
    Gamma |-- <{ new &T t }> is <{{ &T }}>

  | T_NewI : forall Gamma t T,
    Gamma |-- t is <{{ Immut T }}> ->
    Gamma |-- <{ new i&T t }> is <{{ i&T }}>

  | T_LoadM : forall Gamma t T,
    Gamma |-- t is <{{ &T }}> ->
    Gamma |-- <{ *t }> is T

  | T_LoadI : forall Gamma t T,
    Gamma |-- t is <{{ i&T }}> ->
    Gamma |-- <{ *t }> is <{{ Immut T }}>

  | T_Asg : forall Gamma t1 t2 T,
    Gamma |-- t1 is <{{ &T }}> ->
    Gamma |-- t2 is T ->
    Gamma |-- <{ t1 = t2 }> is <{{ Unit }}>

  | T_Var : forall Gamma x T,
    Gamma x = Some T ->
    Gamma |-- <{ var x }> is T

  | T_Fun : forall Gamma x t T Tx,
    Gamma[x <== Tx] |-- t is T ->
    Gamma |-- <{ fn x Tx t }> is <{{ Tx --> T }}>

  | T_Call : forall Gamma t1 t2 Tx T,
    Gamma |-- t1 is <{{ Tx --> T }}> ->
    Gamma |-- t2 is Tx ->
    Gamma |-- <{ call t1 t2 }> is T

  | T_Seq : forall Gamma t1 t2 T1 T2,
    Gamma |-- t1 is T1 ->
    Gamma |-- t2 is T2 ->
    Gamma |-- <{ t1; t2 }> is T2

  | T_Spawn : forall Gamma t T,
    safe Gamma |-- t is T ->
    Gamma |-- <{ spawn t }> is <{{ Unit }}> 

  where "Gamma '|--' t 'is' T" := (type_of Gamma t T).

(* ------------------------------------------------------------------------- *)
(* substitution                                                              *)
(* ------------------------------------------------------------------------- *)

Local Infix "=?" := string_dec (at level 70, no associativity).

Fixpoint subst (x : id) (tx t : tm) : tm :=
  match t with
  | <{ unit        }> => t
  | <{ N _         }> => t
  | <{ & _ :: _    }> => t
  | <{ new T t'    }> => <{ new T ([x := tx] t')            }>
  | <{ *t'         }> => <{ * ([x := tx] t')                }>
  | <{ t1 = t2     }> => <{ ([x := tx] t1) = ([x := tx] t2) }>
  | <{ var x'      }> => if x =? x' then tx else t
  | <{ fn x' Tx t' }> => if x =? x' then t  else <{ fn x' Tx ([x := tx] t') }>
  | <{ call t1 t2  }> => <{ call ([x := tx] t1) ([x := tx] t2) }>
  | <{ t1; t2      }> => <{ ([x := tx] t1) ; ([x := tx] t2)    }>
  | <{ spawn t'    }> => <{ spawn ([x := tx] t')               }>
  end
  where "'[' x ':=' tx ']' t" := (subst x tx t).

(* ------------------------------------------------------------------------- *)
(* operational semantics -- term step                                        *)
(* ------------------------------------------------------------------------- *)

Inductive tstep : tm -> effect -> tm -> Prop :=
  (* New *)
  | TS_New1 : forall t t' e T,
    t --[e]--> t' ->
    <{ new T t }> --[e]--> <{ new T t' }>

  | TS_New : forall ad v T,
    value v ->
    <{ new T v }> --[EF_Alloc ad v T]--> <{ &ad :: T }>

  (* Load *)
  | TS_Load1 : forall t t' e,
    t --[e]--> t' ->
    <{ *t }> --[e]--> <{ *t' }>

  | TS_Load : forall ad t T,
    <{ * &ad :: T }> --[EF_Read ad t]--> t

  (* Asg *)
  | TS_Asg1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{ t1 = t2 }> --[e]--> <{ t1' = t2 }>

  | TS_Asg2 : forall t t' v e,
    value v ->
    t --[e]--> t' ->
    <{ v = t }> --[e]--> <{ v = t' }>

  | TS_Asg : forall ad v T,
    value v ->
    <{ &ad :: T = v }> --[EF_Write ad v T]--> <{ unit }>

  (* Call *)
  | TS_Call1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{ call t1 t2 }> --[e]--> <{ call t1' t2 }>

  | TS_Call2 : forall t t' v e,
    value v ->
    t --[e]--> t' ->
    <{ call v t }> --[e]--> <{ call v t' }>

  | TS_Call : forall x Tx t v,
    value v ->
    <{ call <{ fn x Tx t }> v }> --[EF_None]--> ([x := v] t)

  (* Seq *)
  | TS_Seq1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{ t1; t2 }> --[e]--> <{ t1'; t2 }>

  | TS_Seq : forall v t,
    value v ->
    <{ v; t }> --[EF_None]--> t

  (* Spawn *)
  | TS_Spawn : forall t,
    <{ spawn t }> --[EF_Spawn t]--> <{ unit }>

  where "t '--[' e ']-->' t'" := (tstep t e t').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- memory step                                      *)
(* ------------------------------------------------------------------------- *)

Definition mem := list (tm * typ).
Definition memory_default := (<{ unit }>, <{{ Unit }}>).

Notation " l '[' i '].tm' " := (fst (l[i] or memory_default))
  (at level 9, i at next level).
Notation " l '[' i '].typ' " := (snd (l[i] or memory_default))
  (at level 9, i at next level).

Inductive mstep : mem -> tm -> effect -> mem -> tm -> Prop :=
  | MS_Alloc : forall m t t' ad v T,
    ad = #m ->
    t --[EF_Alloc ad v T]--> t' ->
    m / t ==[EF_Alloc ad v T]==> (m +++ (v, T)) / t'

  | MS_Read : forall m t t' ad,
    ad < #m ->
    t --[EF_Read ad m[ad].tm]--> t' ->
    m / t ==[EF_Read ad m[ad].tm]==> m / t'

  | MS_Write : forall m t t' ad v T,
    ad < #m ->
    t --[EF_Write ad v T]--> t' ->
    m / t ==[EF_Write ad v T]==> m[ad <- (v, T)] / t'

  | MS_None : forall m t t',
    t --[EF_None]--> t' ->
    m / t ==[EF_None]==> m / t'

  where "m / t '==[' e ']==>' m' / t'" := (mstep m t e m' t').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- concurrent step                                  *)
(* ------------------------------------------------------------------------- *)

Definition threads := list tm.
Definition thread_default := <{ unit }>.
Definition thread_id := nat.

Notation " l '[' i ']' " := (l[i] or thread_default)
  (at level 9, i at next level).

Inductive cstep :
  mem -> threads -> thread_id -> effect -> mem -> threads -> Prop :=

  | CS_Spawn : forall m t' ths tid block,
      tid < #ths ->
      ths[tid] --[EF_Spawn block]--> t' ->
      m / ths ~~[tid, EF_Spawn block]~~> m / (ths[tid <- t'] +++ block)

  | CS_Mem : forall m m' t' ths tid e,
      tid < #ths ->
      m / ths[tid] ==[e]==> m' / t' ->
      m / ths ~~[tid, e]~~> m' / ths[tid <- t']

  where "m / ths '~~[' tid ,  e ']~~>' m' / ths'" :=
    (cstep m ths tid e m' ths').

(* ------------------------------------------------------------------------- *)
(* multistep                                                                 *)
(* ------------------------------------------------------------------------- *)

Definition trace := list (thread_id * effect).

Inductive multistep : mem -> threads -> trace -> mem -> threads -> Prop :=
  | cmultistep_refl: forall m ths,
    m / ths ~~[nil]~~>* m / ths (* TODO: nil? *)

  | cmultistep_trans : forall m m' m'' ths ths' ths'' tc tid e,
    m  / ths  ~~[tc]~~>* m'  / ths'  ->
    m' / ths' ~~[tid, e]~~> m'' / ths'' ->
    m  / ths  ~~[(tid, e) :: tc]~~>* m'' / ths''

  where "m / t '~~[' tc ']~~>*' m' / t'" := (multistep m t tc m' t').

