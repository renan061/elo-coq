From Coq Require Import Arith.
From Coq Require Import Strings.String.
From Coq Require Import List.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.

Definition id   := string.
Definition addr := nat.
 
(* ------------------------------------------------------------------------- *)
(* types                                                                     *)
(* ------------------------------------------------------------------------- *)

(* safe type *)
Inductive sty : Set :=
  | ty_unit
  | ty_num
  | ty_refR : sty -> sty (* read reference *)
  | ty_refX : ty  -> sty (* guarded reference *)

(* type *)
with ty : Set :=
  | ty_safe : sty -> ty
  | ty_refW : ty  -> ty (* write reference *)
  | ty_fun  : ty  -> ty -> ty
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
  | tm_fun   : id -> ty -> tm -> tm
  | tm_call  : tm -> tm -> tm
  (* memory *)
  | tm_ref   : addr -> ty -> tm
  | tm_new   : tm   -> ty -> tm
  | tm_load  : tm   -> tm
  | tm_asg   : tm   -> tm -> tm
  | tm_acq   : tm   -> tm -> tm
  | tm_cr    : addr -> tm -> tm       (* critical region  *)
  | tm_ptm   : option nat -> tm -> tm (* protected term   *)
  (* concurrency *)
  | tm_spawn : tm -> tm
  .

(* ------------------------------------------------------------------------- *)
(* notations                                                                 *)
(* ------------------------------------------------------------------------- *)

(* types *)
Declare Custom Entry elo_ty.
Notation "` T `" := T (T custom elo_ty at level 99).
Notation "( x )" := x (in custom elo_ty, x at level 99).
Notation "x"     := x (in custom elo_ty at level 0, x constr at level 0).

(* safe types *)
Notation "'Unit'" := (ty_safe ty_unit)            (in custom elo_ty at level 0).
Notation "'Num'"  := (ty_safe ty_num)             (in custom elo_ty at level 0).
Notation "'r&' T" := (ty_safe (ty_refR T))        (in custom elo_ty at level 5).
Notation "'x&' T" := (ty_safe (ty_refX T))        (in custom elo_ty at level 5).

(* general types *)
Notation "'Safe' T"    := (ty_safe T)             (in custom elo_ty at level 5).
Notation "'w&' T"      := (ty_refW T)             (in custom elo_ty at level 5).
Notation "T1 '-->' T2" := (ty_fun T1 T2)          (in custom elo_ty at level 50,
                                                           right associativity).

(* terms *)
Declare Custom Entry elo_tm.
Notation "<{ t }>" := t (t custom elo_tm at level 99).
Notation "( x )"   := x (in custom elo_tm, x at level 99).
Notation "x"       := x (in custom elo_tm at level 0, x constr at level 0).

Notation "'unit'"         := (tm_unit)            (in custom elo_tm at level 0).
Notation "'nat' n"        := (tm_nat n)           (in custom elo_tm at level 0).
Notation "'var' x"        := (tm_var x)           (in custom elo_tm at level 0).
Notation "'fn' x Tx t"    := (tm_fun x Tx t)       (in custom elo_tm at level 0,
                                                            x constr at level 0,
                                                   Tx custom elo_ty at level 0).
Notation "'call' t1 t2"   := (tm_call t1 t2)      (in custom elo_tm at level 0).
Notation "'&' ad ':' T"   := (tm_ref ad T)         (in custom elo_tm at level 0,
                                                    T custom elo_ty at level 0).
Notation "'new' t : T"    := (tm_new t T)          (in custom elo_tm at level 0,
                                                    T custom elo_ty at level 0).
Notation "'*' t"          := (tm_load t)          (in custom elo_tm at level 0).
Notation "t1 ':=' t2"     := (tm_asg t1 t2)       (in custom elo_tm at level 70,
                                                              no associativity).
Notation "'acq' t1 t2"    := (tm_acq t1 t2)       (in custom elo_tm at level 0).
Notation "'cr' t1 t2"     := (tm_cr t1 t2)        (in custom elo_tm at level 0).
Notation "'ptm' tid t"    := (tm_ptm tid t)       (in custom elo_tm at level 0).
Notation "'spawn' t"      := (tm_spawn t)         (in custom elo_tm at level 0).

Reserved Notation "Gamma '|--' t 'is' T" (at level 40).

Reserved Notation "'[' x ':=' tx ']' t" (in custom elo_tm at level 20,
  x constr).

Reserved Notation "t '--[' e ']-->' t'" (at level 40,
  e at next level).

Reserved Notation "m / t '==[' e ']==>' m' / t'" (at level 40,
  t at next level, e at next level, m' at next level).

Reserved Notation "m / ths '~~[' tid , e ']~~>' m' / ths'" (at level 40,
  ths at next level, tid at next level, e at next level, m' at next level).

Reserved Notation "m / ths '~~[' tc ']~~>*' m' / ths' " (at level 40,
  ths at next level, tc at next level, m' at next level).

(* ------------------------------------------------------------------------- *)
(* values                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive value : tm -> Prop :=
  | v_unit : value <{unit}>
  | v_num  : forall n, value <{nat n}>
  | v_fun  : forall x Tx t, value <{fn x Tx t}> 
  | v_ref  : forall ad T, value <{&ad : T}>
  | v_ptm  : forall ad t, value <{ptm ad t}>
  .

(* ------------------------------------------------------------------------- *)
(* effects                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive eff : Set :=
  | e_none
  | e_alloc (ad : addr) (t : tm) (T : ty)
  | e_read  (ad : addr) (t : tm)
  | e_write (ad : addr) (t : tm) (T : ty)
  | e_spawn (tid : nat) (t : tm)
  | e_acq   (tid : nat) (ad : addr) (t : tm)
  | e_rel   (tid : nat) (ad : addr)
  .

(* ------------------------------------------------------------------------- *)
(* aliases                                                                   *)
(* ------------------------------------------------------------------------- *)

Definition ctx := map ty.

Definition mem     := list (tm * ty).
Definition threads := list tm.
Definition trace   := list (nat * eff).

Definition tm_default  := <{unit}>.
Definition ty_default  := `Unit`.
Definition mem_default := (tm_default, ty_default).
Definition tc_default  := (0, e_none).

(* ------------------------------------------------------------------------- *)
(* typing                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Filters out of the context all variables with non-immutable types. *)
Definition safe (Gamma : ctx) : ctx :=
  fun k => 
    match Gamma k with
    | Some `Safe T` => Some `Safe T`
    | _ => None
    end.

Inductive type_of : ctx -> tm -> ty -> Prop :=
  | T_unit : forall Gamma,
    Gamma |-- <{unit}> is `Unit`

  | T_num : forall Gamma n,
    Gamma |-- <{nat n}> is `Num`

  | T_var : forall Gamma x T,
    Gamma x = Some T ->
    Gamma |-- <{var x}> is T

  | T_fun : forall Gamma x t T Tx,
    Gamma[x <== Tx] |-- t is T ->
    Gamma |-- <{fn x Tx t}> is `Tx --> T`

  | T_call : forall Gamma t1 t2 Tx T,
    Gamma |-- t1 is `Tx --> T` ->
    Gamma |-- t2 is Tx ->
    Gamma |-- <{call t1 t2}> is T

  | T_refR : forall Gamma ad T,
    Gamma |-- <{&ad : r&T}> is `r&T`

  | T_refX : forall Gamma ad T,
    Gamma |-- <{&ad : x&T}> is `x&T`

  | T_refW : forall Gamma ad T,
    Gamma |-- <{&ad : w&T}> is `w&T`

  | T_newR : forall Gamma t T,
    Gamma |-- t is `Safe T` ->
    Gamma |-- <{new t : r&T}> is `r&T`

  | T_newX : forall Gamma t T,
    safe Gamma |-- t is T ->
    Gamma |-- <{new t : x&T}> is `x&T`

  | T_newW : forall Gamma t T,
    Gamma |-- t is T ->
    Gamma |-- <{new t : w&T}> is `w&T`

  | T_loadR : forall Gamma t T,
    Gamma |-- t is `r&T` ->
    Gamma |-- <{*t}> is `Safe T`

  | T_loadW : forall Gamma t T,
    Gamma |-- t is `w&T` ->
    Gamma |-- <{*t}> is T

  | T_asg : forall Gamma t1 t2 T,
    Gamma |-- t1 is `w&T` ->
    Gamma |-- t2 is T ->
    Gamma |-- <{t1 := t2}> is `Unit`

  | T_acq : forall Gamma t1 t2 T1 T2,
    Gamma |-- t1 is `x&T1` ->
    safe Gamma |-- t2 is `T1 --> Safe T2` ->
    Gamma |-- <{acq t1 t2}> is `Safe T2`

  | T_cr : forall Gamma ad t T,
    empty |-- t is T ->
    Gamma |-- <{cr ad t}> is T

  | T_ptm : forall Gamma tid t T,
    empty |-- t is T ->
    Gamma |-- <{ptm tid t}> is T

  | T_spawn : forall Gamma t T,
    safe Gamma |-- t is T ->
    Gamma |-- <{spawn t}> is `Unit` 

  where "Gamma '|--' t 'is' T" := (type_of Gamma t T).

(* ------------------------------------------------------------------------- *)
(* substitution                                                              *)
(* ------------------------------------------------------------------------- *)

Local Infix "=?" := string_dec (at level 70, no associativity).

Fixpoint subst (x : id) (tx t : tm) : tm :=
  match t with
  | <{unit       }> => t
  | <{nat _      }> => t
  (* functions *)
  | <{var x'     }> => if x =? x' then tx else t
  | <{fn x' Tx t'}> => if x =? x' then t  else <{fn x' Tx ([x := tx] t')}>
  (* memory *)
  | <{call t1 t2 }> => <{call ([x := tx] t1) ([x := tx] t2)}>
  | <{& _ : _    }> => t
  | <{new t' : T }> => <{new ([x := tx] t') : T}>
  | <{*t'        }> => <{* ([x := tx] t')}>
  | <{t1 := t2   }> => <{([x := tx] t1) := ([x := tx] t2)}>
  | <{acq t1 t2  }> => <{acq ([x := tx] t1) ([x := tx] t2)}>
  | <{cr ad t'   }> => <{cr ad ([x := tx] t')}> (* could it be "t"? *)
  | <{ptm _ _    }> => t
  (* concurrency *)
  | <{spawn t'   }> => <{spawn ([x := tx] t')}>
  end
  where "'[' x ':=' tx ']' t" := (subst x tx t) (in custom elo_tm).

(* ------------------------------------------------------------------------- *)
(* operational semantics -- term step                                        *)
(* ------------------------------------------------------------------------- *)

Inductive tstep : tm -> eff -> tm -> Prop :=
  (* Call *)
  | ts_call1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{call t1 t2}> --[e]--> <{call t1' t2}>

  | ts_call2 : forall t1 t2 t2' e,
    value t1 ->
    t2 --[e]--> t2' ->
    <{call t1 t2}> --[e]--> <{call t1 t2'}>

  | ts_call : forall x Tx t tx,
    value tx ->
    <{call (fn x Tx t) tx}> --[e_none]--> <{[x := tx] t}>

  (* New *)
  | ts_new1 : forall t t' e T,
    t --[e]--> t' ->
    <{new t : T}> --[e]--> <{new t' : T}>

  | ts_newR : forall ad t T,
    value t ->
    <{new t : r&T}>  --[e_alloc ad t `r&T`]--> <{&ad : r&T}>

  | ts_newX : forall ad t T,
    value t ->
    <{new t : x&T}> --[e_alloc ad <{ptm None t}> `x&T`]--> <{&ad : x&T}>

  | ts_newW : forall ad t T,
    value t ->
    <{new t : w&T}> --[e_alloc ad t `w&T`]--> <{&ad : w&T}>

  (* Load *)
  | ts_load1 : forall t t' e,
    t --[e]--> t' ->
    <{*t}> --[e]--> <{*t'}>

  | ts_load : forall ad t T,
    <{* (&ad : T)}> --[e_read ad t]--> t

  (* Asg *)
  | ts_asg1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{t1 := t2}> --[e]--> <{t1' := t2}>

  | ts_asg2 : forall t1 t2 t2' e,
    value t1 ->
    t2 --[e]--> t2' ->
    <{t1 := t2}> --[e]--> <{t1 := t2'}>

  | ts_asg : forall ad t T,
    value t ->
    <{&ad : T := t}> --[e_write ad t T]--> <{unit}>

  (* Acquire *)
  | ts_acq1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{acq t1 t2}> --[e]--> <{acq t1' t2}>

  | ts_acq2 : forall t1 t2 t2' e,
    value t1 ->
    t2 --[e]--> t2' ->
    <{acq t1 t2}> --[e]--> <{acq t1 t2'}>

  | ts_acq : forall tid ad T x Tx t tx,
    <{acq (&ad : T) (fn x Tx t)}> --[e_acq tid ad tx]--> <{cr ad ([x := tx] t)}>

  (* Critical Region *)
  | ts_cr1 : forall ad t t' e,
    t --[e]--> t' ->
    <{cr ad t}> --[e]--> <{cr ad t'}>

  | ts_cr : forall tid ad t,
    value t ->
    <{cr ad t}> --[e_rel tid ad]--> t

  (* Spawn *)
  | ts_spawn : forall tid t,
    <{spawn t}> --[e_spawn tid t]--> <{unit}>

  where "t '--[' e ']-->' t'" := (tstep t e t').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- memory step                                      *)
(* ------------------------------------------------------------------------- *)

Notation " ths '[' tid ']' " := (ths[tid] or tm_default)
  (at level 9, tid at next level).

Notation " m '[' ad '].tm' " := (fst (m[ad] or mem_default))
  (at level 9, ad at next level).

Notation " m '[' ad '].ty' " := (snd (m[ad] or mem_default))
  (at level 9, ad at next level).

Inductive mstep : mem -> tm -> eff -> mem -> tm -> Prop :=
  | ms_none : forall m t t',
    t --[e_none]--> t' ->
    m / t ==[e_none]==> m / t'

  | ms_alloc : forall m t t' ad te T,
    ad = #m ->
    t --[e_alloc ad te T]--> t' ->
    m / t ==[e_alloc ad te T]==> (m +++ (te, T)) / t'

  | ms_read : forall m t t' ad te,
    ad < #m ->
    te = m[ad].tm ->
    t --[e_read ad te]--> t' ->
    m / t ==[e_read ad te]==> m / t'

  | ms_write : forall m t t' ad te T,
    ad < #m ->
    t --[e_write ad te T]--> t' ->
    m / t ==[e_write ad te T]==> m[ad <- (te, T)] / t'

  | ms_acq : forall m t t' tid ad te T,
    ad < #m ->
    m[ad].tm = <{ptm None te}> ->
    m[ad].ty = T ->
    t --[e_acq tid ad te]--> t' ->
    m / t ==[e_acq tid ad te]==> m[ad <- (tm_ptm (Some tid) te, T)] / t'

  | ms_rel : forall m t t' te tid ad T,
    ad < #m ->
    m[ad].tm = tm_ptm (Some tid) te ->
    m[ad].ty = T ->
    t --[e_rel tid ad]--> t' ->
    m / t ==[e_rel tid ad]==> m[ad <- (tm_ptm None te, T)] / t'

  where "m / t '==[' e ']==>' m' / t'" := (mstep m t e m' t').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- step                                             *)
(* ------------------------------------------------------------------------- *)

Inductive cstep : mem -> threads -> nat -> eff -> mem -> threads -> Prop :=
  | cs_mem : forall m m' t' ths tid e,
    tid < #ths ->
    m / ths[tid] ==[e]==> m' / t' ->
    m / ths ~~[tid, e]~~> m' / ths[tid <- t']

  | cs_spawn : forall m t' te ths tid e,
    tid < #ths ->
    ths[tid] --[e_spawn (#ths) te]--> t' ->
    m / ths ~~[tid, e]~~> m / (ths[tid <- t'] +++ te)

  where "m / ths '~~[' tid , e ']~~>' m' / ths'" := (cstep m ths tid e m' ths').

(* ------------------------------------------------------------------------- *)
(* multistep                                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive multistep : mem -> threads -> trace -> mem -> threads -> Prop :=
  | multistep_refl: forall m ths,
    m / ths ~~[nil]~~>* m / ths

  | multistep_trans : forall m m' m'' ths ths' ths'' tid e tc,
    m  / ths  ~~[tc            ]~~>* m'  / ths'  ->
    m' / ths' ~~[tid, e        ]~~>  m'' / ths'' ->
    m  / ths  ~~[(tid, e) :: tc]~~>* m'' / ths'' 

  where "m / ths '~~[' tc ']~~>*' m' / ths'" := (multistep m ths tc m' ths').

