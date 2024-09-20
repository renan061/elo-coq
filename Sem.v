From Coq Require Import Arith.
From Coq Require Import Strings.String.
From Coq Require Import List.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.

Definition id   := string.
Definition addr := nat.
Definition lock := nat.
 
(* ------------------------------------------------------------------------- *)
(* types                                                                     *)
(* ------------------------------------------------------------------------- *)

(* safe type *)
Inductive styp : Set :=
  | ty_unit
  | ty_num
  | ty_refS : styp -> styp
  | ty_mtx  : typ -> styp

(* type *)
with typ : Set :=
  | ty_safe : styp -> typ
  | ty_refU : typ  -> typ
  | ty_fun  : typ  -> typ -> typ
  .

(* ------------------------------------------------------------------------- *)
(* terms                                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive tm : Set :=
  (* primitives *)
  | tm_unit
  | tm_nat   : nat -> tm
  (* functions *)
  | tm_var   : id -> tm
  | tm_fun   : id -> typ -> tm -> tm
  | tm_call  : tm -> tm  -> tm
  (* memory *)
  | tm_ref   : addr -> typ -> tm
  | tm_new   : typ  -> tm  -> tm
  | tm_load  : tm   -> tm
  | tm_asg   : tm   -> tm  -> tm
  (* concurrency *)
  | tm_spawn : tm -> tm
  (* mutual exclusion *)
  | tm_mtx   : lock -> tm -> tm
  | tm_newx  : tm -> tm
  | tm_acq   : tm -> tm -> tm
  | tm_cr    : lock -> tm -> tm
  .

(* ------------------------------------------------------------------------- *)
(* notations                                                                 *)
(* ------------------------------------------------------------------------- *)

Declare Custom Entry elo_typ.
Notation "<{{ T }}>" := T (T custom elo_typ at level 99).
Notation "( x )"     := x (in custom elo_typ, x at level 99).
Notation "x"         := x (in custom elo_typ at level 0, x constr at level 0).

(* safe types *)
Notation "'Unit'"  := (ty_safe ty_unit)          (in custom elo_typ at level 0).
Notation "'Num'"   := (ty_safe ty_num)           (in custom elo_typ at level 0).
Notation "'s&' T"  := (ty_safe (ty_refS T))      (in custom elo_typ at level 5).
Notation "'Mtx' T" := (ty_safe (ty_mtx T))       (in custom elo_typ at level 0).

(* types *)
Notation "'Safe' T"    := (ty_safe T)            (in custom elo_typ at level 5).
Notation "'u&' T"      := (ty_refU T)            (in custom elo_typ at level 5).
Notation "T1 '-->' T2" := (ty_fun T1 T2)         (in custom elo_typ at level 50,
                                                           right associativity).

Declare Custom Entry elo_tm.
Notation "<{ t }>" := t (t custom elo_tm at level 99).
Notation "{ x }"   := x (in custom elo_tm, x at level 99).
Notation "x"       := x (in custom elo_tm at level 0, x constr at level 0).

Notation "'unit'"        := (tm_unit)             (in custom elo_tm at level 0).
Notation "'nat' n"       := (tm_nat n)            (in custom elo_tm at level 0).
Notation "'var' x"       := (tm_var x)            (in custom elo_tm at level 0).
Notation "'fn' x Tx t"   := (tm_fun x Tx t)        (in custom elo_tm at level 0,
                                                            x constr at level 0,
                                                  Tx custom elo_typ at level 0).
Notation "'call' t1 t2"  := (tm_call t1 t2)       (in custom elo_tm at level 0).
Notation "'&' ad '::' T" := (tm_ref ad T)          (in custom elo_tm at level 0,
                                                   T custom elo_typ at level 0).
Notation "'new' T t"     := (tm_new T t)           (in custom elo_tm at level 0,
                                                   T custom elo_typ at level 0).
Notation "'*' t"         := (tm_load t)           (in custom elo_tm at level 0).
Notation "t1 '=' t2"     := (tm_asg t1 t2)        (in custom elo_tm at level 70,
                                                              no associativity).
Notation "'spawn' t"     := (tm_spawn t)          (in custom elo_tm at level 0).
Notation "'mtx' l t"     := (tm_mtx l t)          (in custom elo_tm at level 0).
Notation "'newx' t"      := (tm_newx t)           (in custom elo_tm at level 0).
Notation "'acq' t1 t2"   := (tm_acq t1 t2)        (in custom elo_tm at level 0).
Notation "'cr' t1 t2"    := (tm_cr t1 t2)         (in custom elo_tm at level 0).

Reserved Notation "Gamma '|--' t 'is' T"
  (at level 40).

Reserved Notation "'[' x ':=' tx ']' t"
  (at level 20, x constr, tx at next level, t at next level).

Reserved Notation "t '--[' e ']-->' t'" (at level 40,
  e at next level).

Reserved Notation "m '--[m' e ']-->' m' " (at level 40,
  e at next level).

Reserved Notation "m / ts '--[c' tid , e ']-->' m' / ts'" (at level 40,
  ts at next level,
  tid at next level, e at next level,
  m' at next level, ts' at next level).

Reserved Notation "m / ts / ls '--[s' tid , e ']-->' m' / ts' / ls' "
  (at level 40,
    ts at next level, ls at next level,
    tid at next level, e at next level,
    m' at next level, ts' at next level).

Reserved Notation "m / ts / ls '--[' tc ']-->*' m' / ts' / ls' " (at level 40,
  ts at next level, ls at next level,
  tc at next level,
  m' at next level, ts' at next level).

(* ------------------------------------------------------------------------- *)
(* values                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive value : tm -> Prop :=
  | v_unit : value <{ unit }> 
  | v_num  : forall n, value <{ nat n }>
  | v_fun  : forall x Tx t, value <{ fn x Tx t }>
  | v_ref  : forall ad T, value <{ &ad :: T }>
  | v_mtx  : forall l t, value <{ mtx l t }>
  .

(* ------------------------------------------------------------------------- *)
(* effects                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive eff : Set :=
  | e_none
  | e_alloc   (ad : addr) (t : tm) (T : typ)
  | e_read    (ad : addr) (t : tm)
  | e_write   (ad : addr) (t : tm) (T : typ)
  | e_spawn   (t : tm)
  | e_newlock (l : lock)
  | e_lock    (l : lock)
  | e_unlock  (l : lock)
  .

(* ------------------------------------------------------------------------- *)
(* typing                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition ctx := map typ.

(* Filters out of the context all variables with non-immutable types. *)
Definition safe (Gamma : ctx) : ctx :=
  fun k => 
    match Gamma k with
    | Some <{{ Safe T }}> => Some <{{ Safe T }}>
    | _ => None
    end.

Inductive type_of : ctx -> tm -> typ -> Prop :=
  | T_unit : forall Gamma,
    Gamma |-- <{ unit }> is <{{ Unit }}>

  | T_num : forall Gamma n,
    Gamma |-- <{ nat n }> is <{{ Num }}>

  | T_var : forall Gamma x T,
    Gamma x = Some T ->
    Gamma |-- <{ var x }> is T

  | T_fun : forall Gamma x t T Tx,
    Gamma[x <== Tx] |-- t is T ->
    Gamma |-- <{ fn x Tx t }> is <{{ Tx --> T }}>

  | T_call : forall Gamma t1 t2 Tx T,
    Gamma |-- t1 is <{{ Tx --> T }}> ->
    Gamma |-- t2 is Tx ->
    Gamma |-- <{ call t1 t2 }> is T

  | T_refU : forall Gamma ad T,
    Gamma |-- <{ &ad :: u&T }> is <{{ u&T }}>

  | T_refS : forall Gamma ad T,
    Gamma |-- <{ &ad :: s&T }> is <{{ s&T }}>

  | T_newU : forall Gamma t T,
    Gamma |-- t is T ->
    Gamma |-- <{ new u&T t }> is <{{ u&T }}>

  | T_newS : forall Gamma t T,
    Gamma |-- t is <{{ Safe T }}> ->
    Gamma |-- <{ new s&T t }> is <{{ s&T }}>

  | T_loadU : forall Gamma t T,
    Gamma |-- t is <{{ u&T }}> ->
    Gamma |-- <{ *t }> is T

  | T_loadS : forall Gamma t T,
    Gamma |-- t is <{{ s&T }}> ->
    Gamma |-- <{ *t }> is <{{ Safe T }}>

  | T_asg : forall Gamma t1 t2 T,
    Gamma |-- t1 is <{{ u&T }}> ->
    Gamma |-- t2 is T ->
    Gamma |-- <{ t1 = t2 }> is <{{ Unit }}>

  | T_spawn : forall Gamma t T,
    safe Gamma |-- t is T ->
    Gamma |-- <{ spawn t }> is <{{ Unit }}> 

  | T_mtx : forall Gamma l t T,
    empty |-- t is T -> (* TODO *)
    Gamma |-- <{ mtx l t }> is <{{ Mtx T }}>

  | T_newx : forall Gamma t T,
    safe Gamma |-- t is T ->
    Gamma |-- <{ newx t }> is <{{ Mtx T }}>

  | T_acq : forall Gamma t1 t2 T1 T2,
    Gamma |-- t1 is <{{ Mtx T1 }}> ->
    safe Gamma |-- t2 is <{{ T1 --> Safe T2 }}> ->
    Gamma |-- <{ acq t1 t2 }> is <{{ Safe T2 }}>

  | T_cr : forall Gamma l t T,
    empty |-- t is T -> (* TODO *)
    Gamma |-- <{ cr l t }> is T

  where "Gamma '|--' t 'is' T" := (type_of Gamma t T).

(* ------------------------------------------------------------------------- *)
(* substitution                                                              *)
(* ------------------------------------------------------------------------- *)

Local Infix "=?" := string_dec (at level 70, no associativity).

Fixpoint subst (x : id) (tx t : tm) : tm :=
  match t with
  | <{ unit        }> => t
  | <{ nat _       }> => t
  | <{ & _ :: _    }> => t
  | <{ new T t'    }> => <{ new T ([x := tx] t')            }>
  | <{ *t'         }> => <{ * ([x := tx] t')                }>
  | <{ t1 = t2     }> => <{ ([x := tx] t1) = ([x := tx] t2) }>
  | <{ var x'      }> => if x =? x' then tx else t
  | <{ fn x' Tx t' }> => if x =? x' then t  else <{ fn x' Tx ([x := tx] t') }>
  | <{ call t1 t2  }> => <{ call ([x := tx] t1) ([x := tx] t2) }>
  | <{ spawn t'    }> => <{ spawn ([x := tx] t')               }>
  (* TODO *)
  | tm_mtx  _ _ => <{ unit }>
  | tm_newx _   => <{ unit }>
  | tm_acq  _ _ => <{ unit }>
  | tm_cr   _ _ => <{ unit }>
  end
  where "'[' x ':=' tx ']' t" := (subst x tx t).

(* ------------------------------------------------------------------------- *)
(* operational semantics -- term step                                        *)
(* ------------------------------------------------------------------------- *)

Inductive tstep : tm -> eff -> tm -> Prop :=
  (* Call *)
  | ts_call1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{ call t1 t2 }> --[e]--> <{ call t1' t2 }>

  | ts_call2 : forall t1 t2 t2' e,
    value t1 ->
    t2 --[e]--> t2' ->
    <{ call t1 t2 }> --[e]--> <{ call t1 t2' }>

  | ts_call : forall x Tx t tx,
    value tx ->
    <{ call {fn x Tx t} tx }> --[e_none]--> ([x := tx] t)

  (* New *)
  | ts_new1 : forall t t' e T,
    t --[e]--> t' ->
    <{ new T t }> --[e]--> <{ new T t' }>

  | ts_new : forall ad t T,
    value t ->
    <{ new T t }> --[e_alloc ad t T]--> <{ &ad :: T }>

  (* Load *)
  | ts_load1 : forall t t' e,
    t --[e]--> t' ->
    <{ *t }> --[e]--> <{ *t' }>

  | ts_load : forall ad t T,
    <{ * &ad :: T }> --[e_read ad t]--> t

  (* Asg *)
  | ts_asg1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{ t1 = t2 }> --[e]--> <{ t1' = t2 }>

  | ts_asg2 : forall t1 t2 t2' e,
    value t1 ->
    t2 --[e]--> t2' ->
    <{ t1 = t2 }> --[e]--> <{ t1 = t2' }>

  | ts_asg : forall ad t T,
    value t ->
    <{ {&ad :: T} = t }> --[e_write ad t T]--> <{ unit }>

  (* Spawn *)
  | ts_spawn : forall t,
    <{ spawn t }> --[e_spawn t]--> <{ unit }>

  (* New Mutex *)
  | ts_newx1 : forall t t' e,
    t --[e]--> t' ->
    <{ newx t }> --[e]--> <{ newx t' }>

  | ts_newx : forall t l,
    value t ->
    <{ newx t }> --[e_newlock l]--> <{ mtx l t }>

  (* Acquire *)
  | ts_acq1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{ acq t1 t2 }> --[e]--> <{ acq t1' t2 }>

  | ts_acq2 : forall t1 t2 t2' e,
    value t1 ->
    t2 --[e]--> t2' ->
    <{ acq t1 t2 }> --[e]--> <{ acq t1 t2' }>

  | ts_acq : forall l x Tx t tx,
    <{ acq {mtx l tx} {fn x Tx t} }> --[e_lock l]--> <{ cr l ([x := tx] t) }>

  (* Critical Region *)
  | ts_cr1 : forall l t t' e,
    t --[e]--> t' ->
    <{ cr l t }> --[e]--> <{ cr l t' }>

  | ts_cr : forall l t,
    value t ->
    <{ cr l t }> --[e_unlock l]--> t

  where "t '--[' e ']-->' t'" := (tstep t e t').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- memory step                                      *)
(* ------------------------------------------------------------------------- *)

Definition mem := list (tm * typ).
Definition memory_default := (<{ unit }>, <{{ Unit }}>).

Notation " l '[' i '].tm' " := (fst (l[i] or memory_default))
  (at level 9, i at next level).
Notation " l '[' i '].ty' " := (snd (l[i] or memory_default))
  (at level 9, i at next level).

Inductive mstep : mem -> eff -> mem -> Prop :=
  | ms_alloc : forall m t T,
    m --[m e_alloc (#m) t T]--> (m +++ (t, T))

  | ms_read : forall m ad,
    ad < #m ->
    m --[m e_read ad m[ad].tm]--> m

  | ms_write : forall m ad te T,
    ad < #m ->
    m --[m e_write ad te T]--> m[ad <- (te, T)]

  where "m '--[m' e ']-->' m' " := (mstep m e m').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- concurrent step                                  *)
(* ------------------------------------------------------------------------- *)

Definition threads := list tm.
Definition thread_default := <{ unit }>.

Notation " l '[' i ']' " := (l[i] or thread_default)
  (at level 9, i at next level).

Inductive cstep : mem -> threads -> nat -> eff -> mem -> threads -> Prop :=
  | cs_spawn : forall m ts t' tid te,
      tid < #ts ->
      ts[tid] --[e_spawn te]--> t' ->
      m / ts --[c tid, e_spawn te]--> m / (ts[tid <- t'] +++ te)

  | cs_mem : forall m m' ts t' tid e,
      tid < #ts ->
      m / ts[tid] --[m e]--> m' / t' ->
      m / ts --[c tid, e]--> m' / ts[tid <- t']

    where "m / ts '--[c' tid ,  e ']-->' m' / ts'" :=
      (cstep m ts tid e m' ts').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- sync step                                        *)
(* ------------------------------------------------------------------------- *)

Definition locks := list (option nat).

Inductive sstep :
  mem -> threads -> locks -> nat -> eff -> mem -> threads -> locks -> Prop :=

  | ss_newlock : forall m m' ls ts ts' tid l,
    l = #ls ->
    m / ts --[c tid, e_newlock l]--> m' / ts' ->
    m / ts / ls --[s tid, e_newlock l]--> m / ts' / (ls +++ None)

  | ss_lock : forall m m' ls ts ts' tid l,
    l < #ls ->
    ls[l] or None = None ->
    m / ts --[c tid, e_lock l]--> m' / ts' ->
    m / ts / ls --[s tid, e_lock l]--> m / ts' / ls[l <- Some tid]

  | ss_unlock : forall m m' ls ts ts' tid l,
    l < #ls ->
    ls[l] or None = Some tid ->
    m / ts --[c tid, e_unlock l]--> m' / ts' ->
    m / ts / ls --[s tid, e_unlock l]--> m / ts' / ls[l <- None]

  | ss_conc : forall m m' ls ts ts' tid e,
    m / ts --[c tid, e]--> m' / ts' ->
    m / ts / ls --[s tid, e]--> m' / ts' / ls

  where "m / ls / ts '--[s' tid , e ']-->' m' / ls' / ts'" :=
    (sstep m ls ts tid e m' ls' ts').

(* ------------------------------------------------------------------------- *)
(* multistep                                                                 *)
(* ------------------------------------------------------------------------- *)

Definition trace := list (nat * eff).

Inductive multistep :
  mem -> threads -> locks -> trace -> mem -> threads -> locks -> Prop :=

  | multistep_refl: forall m ls ts,
    m / ls / ts --[nil]-->* m / ls / ts

  | multistep_trans : forall m m' m'' ts ts' ts'' ls ls' ls'' tid e tc,
    m  / ts  / ls  --[tc            ]-->* m'  / ts'  / ls'  ->
    m' / ts' / ls' --[s tid, e      ]-->  m'' / ts'' / ls'' ->
    m  / ts  / ls  --[(tid, e) :: tc]-->* m'' / ts'' / ls'' 

  where "m / ts / ls '--[' tc ']-->*' m' / ts' / ls'" :=
    (multistep m ts ls tc m' ts' ls').

