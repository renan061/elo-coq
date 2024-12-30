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
  | ty_nat
  | ty_refR : sty -> sty      (* read reference    *)
  | ty_refX : ty  -> sty      (* monitor reference *)

(* type *)
with ty : Set :=
  | ty_safe : sty -> ty
  | ty_refW : ty  -> ty       (* write reference   *)
  | ty_fun  : ty  -> ty -> ty
  .

(* ------------------------------------------------------------------------- *)
(* terms                                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive tm : Set :=
  (* primitives *)
  | tm_unit
  | tm_nat   : nat  -> tm
  (* utility *)
  | tm_seq   : tm   -> tm -> tm
  | tm_if    : tm   -> tm -> tm -> tm
  | tm_while : tm   -> tm -> tm
  (* functions *)
  | tm_var   : id   -> tm
  | tm_fun   : id   -> ty -> tm -> tm
  | tm_call  : tm   -> tm -> tm
  (* memory *)
  | tm_ref   : addr -> ty -> tm
  | tm_new   : tm   -> ty -> tm
  | tm_init  : addr -> tm -> ty -> tm
  | tm_load  : tm   -> tm
  | tm_asg   : tm   -> tm -> tm
  | tm_acq   : tm   -> id -> tm -> tm
  | tm_cr    : addr -> tm -> tm
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
Notation "'Nat'"  := (ty_safe ty_nat)             (in custom elo_ty at level 0).
Notation "'r&' T" := (ty_safe (ty_refR T))        (in custom elo_ty at level 5).
Notation "'x&' T" := (ty_safe (ty_refX T))        (in custom elo_ty at level 5).

(* general types *)
Notation "'Safe' T"    := (ty_safe T)             (in custom elo_ty at level 5).
Notation "'w&' T"      := (ty_refW T)             (in custom elo_ty at level 5).
Notation "T1 '-->' T2" := (ty_fun T1 T2)          (in custom elo_ty at level 50,
                                                           right associativity).

(* terms -------------------------------------------------------------------- *)
Declare Custom Entry elo_tm.
Notation "<{ t }>" := t (t custom elo_tm at level 99).
Notation "( x )"   := x (in custom elo_tm, x at level 99).
Notation "x"       := x (in custom elo_tm at level 0, x constr at level 0).

(* primitives --------------------------------------------------------------- *)
Notation "'unit'"  := (tm_unit)  (in custom elo_tm at level 0).
Notation "'nat' n" := (tm_nat n) (in custom elo_tm at level 0,
                                          n constr at level 0).
(* utility ------------------------------------------------------------------ *)
Notation "t1 ';' t2"                         := (tm_seq t1 t2)
 (in custom elo_tm at level 90, right associativity)
                                                                               .
Notation "'if' t1 'then' t2 'else' t3 'end'" := (tm_if t1 t2 t3)
 (in custom elo_tm at level 89,
                t1 at level 99,
                t2 at level 99,
                t3 at level 99).
Notation "'while' t1 'do' t2 'end'" := (tm_while t1 t2)
 (in custom elo_tm at level 89,
                t1 at level 99,
                t2 at level 99).
(* functions ---------------------------------------------------------------- *)
Notation "'var' x"          := (tm_var x)         (in custom elo_tm at level 0).
Notation "'fn' x Tx t"      := (tm_fun x Tx t)     (in custom elo_tm at level 0,
                                                            x constr at level 0,
                                                   Tx custom elo_ty at level 0).
Notation "'call' t1 t2"     := (tm_call t1 t2)    (in custom elo_tm at level 0).
(* memory ------------------------------------------------------------------- *)
Notation "'&' ad ':' T"     := (tm_ref ad T)       (in custom elo_tm at level 0,
                                                    T custom elo_ty at level 0).
Notation "'new' t : T"      := (tm_new t T)        (in custom elo_tm at level 0,
                                                    T custom elo_ty at level 0).
Notation "'init' ad t : T"  := (tm_init ad t T)    (in custom elo_tm at level 0,
                                                    T custom elo_ty at level 0).
Notation "'*' t"            := (tm_load t)        (in custom elo_tm at level 0).
Notation "t1 ':=' t2"       := (tm_asg t1 t2)     (in custom elo_tm at level 70,
                                                              no associativity).
Notation "'acq' t1 x t2"    := (tm_acq t1 x t2)   (in custom elo_tm at level 0).
Notation "'cr' ad t"        := (tm_cr ad t)       (in custom elo_tm at level 0).
(* concurrency -------------------------------------------------------------- *)
Notation "'spawn' t"        := (tm_spawn t)       (in custom elo_tm at level 0).

(* syntactic sugars --------------------------------------------------------- *)
Notation "'let' x ':' Tx '=' tx 'in' t" := <{call (fn x Tx t) tx}>
  (in custom elo_tm at level 10,
           x constr at level 0,
   Tx custom elo_ty at level 0).

(* -------------------------------------------------------------------------- *)

Reserved Notation "'[' x ':=' tx ']' t" (in custom elo_tm at level 20,
  x constr).

Reserved Notation "Gamma '|--' t 'is' T" (at level 40).

Reserved Notation "t '--[' e ']-->' t'" (at level 40,
  e at next level).

Reserved Notation "m / t '==[' e ']==>' m' / t'" (at level 40,
  t at next level, e at next level, m' at next level).

Reserved Notation "m / ths '~~[' tid , e ']~~>' m' / ths'" (at level 40,
  ths at next level, tid at next level, e at next level, m' at next level).

Reserved Notation "m / ths '~~~[' tid , e ']~~>' m' / ths'" (at level 40,
  ths at next level, tid at next level, e at next level, m' at next level).

Reserved Notation "m / ths '~~[' tc ']~~>*' m' / ths'" (at level 40,
  ths at next level, tc at next level, m' at next level).

(* ------------------------------------------------------------------------- *)
(* values                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive value : tm -> Prop :=
  | v_unit : value <{unit}>
  | v_num  : forall n, value <{nat n}>
  | v_fun  : forall x Tx t, value <{fn x Tx t}> 
  | v_ref  : forall ad T, value <{&ad : T}>
  .

(* ------------------------------------------------------------------------- *)
(* effects                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive eff : Set :=
  | e_none
  | e_alloc  (ad : addr) (T : ty)
  | e_insert (ad : addr) (t : tm) (T : ty)
  | e_read   (ad : addr) (t : tm)
  | e_write  (ad : addr) (t : tm)
  | e_acq    (ad : addr) (t : tm)
  | e_rel    (ad : addr)
  | e_spawn  (tid : nat) (t : tm)
  .

(* ------------------------------------------------------------------------- *)
(* cells                                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive region : Set :=
  | R_invalid
  | R_tid  : nat  -> region
  | R_ad   : addr -> region
  .

Inductive cell : Type :=
  | _cell (t : option tm) (T : ty) (X : bool) (R : region)
  .

Notation "'(' t ',' T ',' X ',' R ')'" := (_cell t T X R).

Definition get_cell_t (c : cell) := let (t, _, _, _) := c in t.
Definition get_cell_T (c : cell) := let (_, T, _, _) := c in T.
Definition get_cell_X (c : cell) := let (_, _, X, _) := c in X.
Definition get_cell_R (c : cell) := let (_, _, _, R) := c in R.

Notation " c '.t' " := (get_cell_t c) (at level 9).
Notation " c '.T' " := (get_cell_T c) (at level 9).
Notation " c '.X' " := (get_cell_X c) (at level 9).
Notation " c '.R' " := (get_cell_R c) (at level 9).

(* ------------------------------------------------------------------------- *)
(* aliases                                                                   *)
(* ------------------------------------------------------------------------- *)

Definition ctx     := map ty.
Definition mem     := list cell.
Definition threads := list tm.
Definition trace   := list (nat * eff).

Notation tm_default     := <{unit}>.
Notation ty_default     := `Unit`.
Notation cell_default   := (None, ty_default, false, R_invalid).

(* ------------------------------------------------------------------------- *)
(* typing                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Filters out of the context all variables with types that are not safe. *)
Definition safe (Gamma : ctx) : ctx :=
  fun k => 
    match Gamma k with
    | Some `Safe T` => Some `Safe T`
    | _ => None
    end.

Inductive type_of : ctx -> tm -> ty -> Prop :=
  | T_unit : forall Gamma,
    Gamma |-- <{unit}> is `Unit`

  | T_nat : forall Gamma n,
    Gamma |-- <{nat n}> is `Nat`

  | T_seq : forall Gamma t1 t2 T1 T2,
    Gamma |-- t1 is T1 ->
    Gamma |-- t2 is T2 ->
    Gamma |-- <{t1; t2}> is T2

  | T_if : forall Gamma t1 t2 t3 T,
    Gamma |-- t1 is `Nat` ->
    Gamma |-- t2 is T ->
    Gamma |-- t3 is T ->
    Gamma |-- <{if t1 then t2 else t3 end}> is T

  | T_while : forall Gamma t1 t2 T,
    Gamma |-- t1 is `Nat` ->
    Gamma |-- t2 is T ->
    Gamma |-- <{while t1 do t2 end}> is `Unit`

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

  | T_initR : forall Gamma ad t T,
    Gamma |-- t is `Safe T` ->
    Gamma |-- <{init ad t : r&T}> is `r&T`

  | T_initX : forall Gamma ad t T,
    Gamma |-- t is T ->
    Gamma |-- <{init ad t : x&T}> is `x&T`

  | T_initW : forall Gamma ad t T,
    Gamma |-- t is T ->
    Gamma |-- <{init ad t : w&T}> is `w&T`

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

  | T_acq : forall Gamma t1 x t2 Tx T,
    Gamma |-- t1 is `x&Tx` ->
    (safe Gamma)[x <== Tx] |-- t2 is `Safe T` ->
    Gamma |-- <{acq t1 x t2}> is `Safe T`

  | T_cr : forall Gamma ad t T,
    empty |-- t is T ->
    Gamma |-- <{cr ad t}> is T

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
  | <{unit                     }> => t
  | <{nat _                    }> => t
  (* utility *)
  | <{t1; t2                   }> => <{([x := tx] t1); ([x := tx] t2)}>
  | <{if t1 then t2 else t3 end}> => <{if [x := tx]t1
                                        then [x := tx]t2
                                        else [x := tx]t3
                                       end}>
  | <{while t1 do t2 end       }> => <{while [x := tx]t1 do [x := tx]t2 end}>
  (* functions *)
  | <{var x'        }> => if x =? x' then tx else t
  | <{fn x' Tx t'   }> => if x =? x' then t  else <{fn x' Tx ([x := tx] t')}>
  (* memory *)
  | <{call t1 t2    }> => <{call ([x := tx] t1) ([x := tx] t2)}>
  | <{& _ : _       }> => t
  | <{new t' : T    }> => <{new ([x := tx] t') : T}>
  | <{init ad t' : T}> => <{init ad ([x := tx] t') : T}>
  | <{*t'           }> => <{* ([x := tx] t')}>
  | <{t1 := t2      }> => <{([x := tx] t1) := ([x := tx] t2)}>
  | <{acq t1 x' t2  }> => if x =? x'
                            then <{acq ([x := tx] t1) x' t2            }>
                            else <{acq ([x := tx] t1) x' ([x := tx] t2)}>
  | <{cr ad t'      }> => <{cr ad ([x := tx] t')}>
  (* concurrency *)
  | <{spawn t'      }> => <{spawn ([x := tx] t')}>
  end
  where "'[' x ':=' tx ']' t" := (subst x tx t) (in custom elo_tm).

(* ------------------------------------------------------------------------- *)
(* operational semantics -- term step                                        *)
(* ------------------------------------------------------------------------- *)

Inductive tstep : tm -> eff -> tm -> Prop :=
  (* seq *)
  | ts_seq1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{t1; t2}> --[e]--> <{t1'; t2}>

  | ts_seq : forall t1 t2,
    value t1 ->
    <{t1; t2}> --[e_none]--> t2

  (* if *)
  | ts_if1 : forall t1 t1' t2 t3 e,
    t1 --[e]--> t1' ->
    <{if t1 then t2 else t3 end}> --[e]--> <{if t1' then t2 else t3 end}>

  | ts_ifT : forall n t1 t2,
    <{if nat (S n) then t1 else t2 end}> --[e_none]--> t1

  | ts_ifF : forall t1 t2,
    <{if nat 0 then t1 else t2 end}> --[e_none]--> t2

  (* while *)
  | ts_while : forall t1 t2,
    <{while t1 do t2 end}> --[e_none]--> <{if t1
                                            then t2; while t1 do t2 end
                                            else unit
                                           end}>

  (* call *)
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

  (* new *)
  | ts_new : forall ad t T,
    <{new t : T}> --[e_alloc ad T]--> <{init ad t : T}>

  (* init *)
  | ts_init1 : forall ad t t' e T,
    t --[e]--> t' ->
    <{init ad t : T}> --[e]--> <{init ad t' : T}>

  | ts_init : forall ad t T,
    value t ->
    <{init ad t : T}> --[e_insert ad t T]--> <{&ad : T}>

  (* load *)
  | ts_load1 : forall t t' e,
    t --[e]--> t' ->
    <{*t}> --[e]--> <{*t'}>

  | ts_load : forall ad t T,
    <{* (&ad : T)}> --[e_read ad t]--> t

  (* asg *)
  | ts_asg1 : forall t1 t1' t2 e,
    t1 --[e]--> t1' ->
    <{t1 := t2}> --[e]--> <{t1' := t2}>

  | ts_asg2 : forall t1 t2 t2' e,
    value t1 ->
    t2 --[e]--> t2' ->
    <{t1 := t2}> --[e]--> <{t1 := t2'}>

  | ts_asg : forall ad t T,
    value t ->
    <{&ad : T := t}> --[e_write ad t]--> <{unit}>

  (* acq *)
  | ts_acq1 : forall t1 t1' x t2 e,
    t1 --[e]--> t1' ->
    <{acq t1 x t2}> --[e]--> <{acq t1' x t2}>

  | ts_acq : forall ad T x t tx,
    <{acq (&ad : T) x t}> --[e_acq ad tx]--> <{cr ad ([x := tx] t)}>

  (* cr *)
  | ts_cr1 : forall ad t t' e,
    t --[e]--> t' ->
    <{cr ad t}> --[e]--> <{cr ad t'}>

  | ts_cr : forall ad t,
    value t ->
    <{cr ad t}> --[e_rel ad]--> t

  (* spawn *)
  | ts_spawn : forall tid t,
    <{spawn t}> --[e_spawn tid t]--> <{unit}>

  where "t '--[' e ']-->' t'" := (tstep t e t').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- memory step                                      *)
(* ------------------------------------------------------------------------- *)

Notation " m '[' ad '].cell' " := (m[ad] or cell_default)
  (at level 9, ad at next level).

Notation " m '[' ad '].t' " := ((m[ad] or cell_default).t)
  (at level 9, ad at next level).

Notation " m '[' ad '].T' " := ((m[ad] or cell_default).T)
  (at level 9, ad at next level).

Notation " m '[' ad '].X' " := ((m[ad] or cell_default).X)
  (at level 9, ad at next level).

Notation " m '[' ad '].R' " := ((m[ad] or cell_default).R)
  (at level 9, ad at next level).

Notation " m '[' ad '.t' '<-' t ']' " :=
  (m[ad <- (Some t, m[ad].T, m[ad].X, m[ad].R)])
  (at level 9, ad at next level, t at next level).

Notation " m '[' ad '.X' '<-' X ']' " :=
  (m[ad <- (m[ad].t, m[ad].T, X, m[ad].R)])
  (at level 9, ad at next level).

Notation " m '[' ad '.R' '<-' R ']' " :=
  (m[ad <- (m[ad].t, m[ad].T, m[ad].X, R)])
  (at level 9, ad at next level).

Inductive mstep : mem -> tm -> eff -> mem -> tm -> Prop :=
  | ms_none : forall m t1 t2,
    t1 --[e_none]--> t2 ->
    m / t1 ==[e_none]==> m / t2

  | ms_alloc : forall m t1 t2 ad T,
    ad = #m ->
    t1 --[e_alloc ad T]--> t2 ->
    m / t1 ==[e_alloc ad T]==> (m +++ (None, T, false, R_invalid)) / t2

  | ms_insert : forall m t1 t2 ad t T,
    ad < #m ->
    t1 --[e_insert ad t T]--> t2 ->
    m / t1 ==[e_insert ad t T]==> m[ad.t <- t] / t2

  | ms_read : forall m t1 t2 ad t,
    ad < #m ->
    m[ad].t = Some t ->
    t1 --[e_read ad t]--> t2 ->
    m / t1 ==[e_read ad t]==> m / t2

  | ms_write : forall m t1 t2 ad t,
    ad < #m ->
    t1 --[e_write ad t]--> t2 ->
    m / t1 ==[e_write ad t]==> m[ad.t <- t] / t2

  | ms_acq : forall m t1 t2 ad t,
    ad < #m ->
    m[ad].t = Some t ->
    m[ad].X = false ->
    t1 --[e_acq ad t]--> t2 ->
    m / t1 ==[e_acq ad t]==> m[ad.X <- true] / t2

  | ms_rel : forall m t1 t2 ad,
    ad < #m ->
    t1 --[e_rel ad]--> t2 ->
    m / t1 ==[e_rel ad]==> m[ad.X <- false] / t2

  where "m / t '==[' e ']==>' m' / t'" := (mstep m t e m' t').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- concurrent step                                  *)
(* ------------------------------------------------------------------------- *)

Notation " ths '[' tid ']' " := (ths[tid] or tm_default)
  (at level 9, tid at next level).

Inductive cstep : mem -> threads -> nat -> eff -> mem -> threads -> Prop :=
  | cs_mem : forall m1 m2 t ths tid e,
    tid < #ths ->
    m1 / ths[tid] ==[e]==> m2 / t ->
    m1 / ths ~~[tid, e]~~> m2 / ths[tid <- t]

  | cs_spawn : forall m t te ths tid,
    tid < #ths ->
    ths[tid] --[e_spawn (#ths) te]--> t ->
    m / ths ~~[tid, e_spawn (#ths) te]~~> m / (ths[tid <- t] +++ te)

  where "m / ths '~~[' tid , e ']~~>' m' / ths'" := (cstep m ths tid e m' ths').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- region step                                      *)
(* ------------------------------------------------------------------------- *)

Definition is_value (t : tm) :=
  match t with
  | <{unit    }> => true
  | <{nat _   }> => true
  | <{fn _ _ _}> => true
  | <{&_ : _  }> => true
  | _            => false
  end.

Definition is_refX  (T : ty) :=
  match T with
  | `x&_` => true
  | _     => false
  end.

(* get-current-region *)
Fixpoint gcr (t' : tm) (R : region) : region :=
  match t' with
  | <{unit                  }> => R
  | <{nat _                 }> => R
  | <{t1; t2                }> => if is_value t1 then gcr t2 R else gcr t1 R
  | <{if t then _ else _ end}> => if is_value t then R else gcr t R
  | <{while _ do _ end      }> => R
  | <{var _                 }> => R
  | <{fn _ _ _              }> => R
  | <{call t1 t2            }> => if is_value t1 then gcr t2 R else gcr t1 R
  | <{&_ : _                }> => R
  | <{new _ : _             }> => R
  | <{init ad t : T         }> => if is_refX T then gcr t (R_ad ad) else gcr t R
  | <{*t                    }> => gcr t R
  | <{t1 := t2              }> => if is_value t1 then gcr t2 R else gcr t1 R
  | <{acq t1 _ _            }> => gcr t1 R
  | <{cr ad t               }> => gcr t (R_ad ad)
  | <{spawn _               }> => R
  end.

Inductive rstep : mem -> threads -> nat -> eff -> mem -> threads -> Prop :=
  | rs_none : forall m1 m2 ths1 ths2 tid,
    m1 / ths1 ~~[tid, e_none]~~> m2 / ths2 ->
    m1 / ths1 ~~~[tid, e_none]~~> m2 / ths2

  | rs_alloc : forall m1 m2 ths1 ths2 tid ad T R,
    R = gcr ths1[tid] (R_tid tid) ->
    m1 / ths1 ~~[tid, e_alloc ad T]~~> m2 / ths2 ->
    m1 / ths1 ~~~[tid, e_alloc ad T]~~> m2[ad.R <- R] / ths2

  | rs_insert : forall m1 m2 ths1 ths2 tid ad t T,
    m1 / ths1 ~~[tid, e_insert ad t T]~~> m2 / ths2 ->
    m1 / ths1 ~~~[tid, e_insert ad t T]~~> m2 / ths2

  | rs_read : forall m1 m2 ths1 ths2 tid ad t,
    m1 / ths1 ~~[tid, e_read ad t]~~> m2 / ths2 ->
    m1 / ths1 ~~~[tid, e_read ad t]~~> m2 / ths2

  | rs_write : forall m1 m2 ths1 ths2 tid ad t,
    m1 / ths1 ~~[tid, e_write ad t]~~> m2 / ths2 ->
    m1 / ths1 ~~~[tid, e_write ad t]~~> m2 / ths2

  | rs_acq : forall m1 m2 ths1 ths2 tid ad t,
    m1 / ths1 ~~[tid, e_acq ad t]~~> m2 / ths2 ->
    m1 / ths1 ~~~[tid, e_acq ad t]~~> m2 / ths2

  | rs_rel : forall m1 m2 ths1 ths2 tid ad,
    m1 / ths1 ~~[tid, e_rel ad]~~> m2 / ths2 ->
    m1 / ths1 ~~~[tid, e_rel ad]~~> m2 / ths2

  | rs_spawn : forall m1 m2 ths1 ths2 tid tid' t',
    m1 / ths1 ~~[tid, e_spawn tid' t']~~> m2 / ths2 ->
    m1 / ths1 ~~~[tid, e_spawn tid' t']~~> m2 / ths2

  where "m / ths '~~~[' tid , e ']~~>' m' / ths'" :=
    (rstep m ths tid e m' ths').

(* ------------------------------------------------------------------------- *)
(* multistep                                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive multistep : mem -> threads -> trace -> mem -> threads -> Prop :=
  | multistep_refl: forall m ths,
    m / ths ~~[nil]~~>* m / ths

  | multistep_trans : forall m1 m2 m3 ths1 ths2 ths3 tid e tc,
    m1 / ths1 ~~[tc            ]~~>* m2 / ths2 ->
    m2 / ths2 ~~~[tid, e       ]~~>  m3 / ths3 ->
    m1 / ths1 ~~[(tid, e) :: tc]~~>* m3 / ths3 

  where "m1 / ths1 '~~[' tc ']~~>*' m2 / ths2" :=
    (multistep m1 ths1 tc m2 ths2).

(* ------------------------------------------------------------------------- *)
(* base                                                                      *)
(* ------------------------------------------------------------------------- *)

Definition base (t : tm) : threads := t :: nil.

