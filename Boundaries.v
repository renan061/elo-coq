
(* ------------------------------------------------------------------------- *)
(* safe-value                                                                *)
(* ------------------------------------------------------------------------- *)

Inductive safe_value : tm -> Prop :=
  | safe_value_unit :
    safe_value <{unit}>

  | safe_value_nat : forall n,
    safe_value <{nat n}>

  | safe_value_refR : forall ad T,
    safe_value <{&ad : r&T}>

  | safe_value_refX : forall ad T,
    safe_value <{&ad : x&T}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-term                                                                 *)
(* ------------------------------------------------------------------------- *)

(* A safe term has no "write" references. *)
Inductive safe_term : tm -> Prop :=
  | safe_term_unit :
    safe_term <{unit}>

  | safe_term_nat : forall n,
    safe_term <{nat n}>

  | safe_term_var : forall x,
    safe_term <{var x}>

  | safe_term_fun : forall x Tx t,
    safe_term t ->
    safe_term <{fn x Tx t}>

  | safe_term_call : forall t1 t2,
    safe_term t1 ->
    safe_term t2 ->
    safe_term <{call t1 t2}>

  | safe_term_refR : forall ad T,
    safe_term <{&ad : r&T}>

  | safe_term_refX : forall ad T,
    safe_term <{&ad : x&T}>

  | safe_term_new : forall T t,
    safe_term t ->
    safe_term <{new t : T}>

  | safe_term_load : forall t,
    safe_term t ->
    safe_term <{*t}>

  | safe_term_asg : forall t1 t2,
    safe_term t1 ->
    safe_term t2 ->
    safe_term <{t1 := t2}>

  | safe_term_acq : forall t1 t2,
    safe_term t1 ->
    safe_term t2 ->
    safe_term <{acq t1 t2}>

  | safe_term_cr : forall ad t,
    safe_term t ->
    safe_term <{cr ad t}>

  | safe_term_spawn : forall t,
    safe_term t ->
    safe_term <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-boundaries                                                           *)
(* ------------------------------------------------------------------------- *)

(* A term is safely bounded if ... *)
Inductive safe_boundaries : tm -> Prop :=
  | safe_boundaries_unit :
    safe_boundaries <{unit}>

  | safe_boundaries_nat : forall n,
    safe_boundaries <{nat n}>

  | safe_boundaries_var : forall x,
    safe_boundaries <{var x}>

  | safe_boundaries_fun : forall x Tx t,
    safe_boundaries t ->
    safe_boundaries <{fn x Tx t}>

  | safe_boundaries_call : forall t1 t2,
    safe_boundaries t1 ->
    safe_boundaries t2 ->
    safe_boundaries <{call t1 t2}>

  | safe_boundaries_ref : forall ad T,
    safe_boundaries <{&ad : T}>

  | safe_boundaries_new : forall T t,
    safe_boundaries t ->
    safe_boundaries <{new t : T}>

  | safe_boundaries_load : forall t,
    safe_boundaries t ->
    safe_boundaries <{*t}>

  | safe_boundaries_asg : forall t1 t2,
    safe_boundaries t1 ->
    safe_boundaries t2 ->
    safe_boundaries <{t1 := t2}>

  | safe_boundaries_acq1 : forall t1 t2,
    ~ value t2 ->
    safe_boundaries t1 ->
    safe_boundaries t2 ->
    safe_boundaries <{acq t1 t2}>

  | safe_boundaries_acq2 : forall t1 t2,
    value t2 ->
    safe_value t2 ->
    safe_boundaries <{acq t1 t2}>

  | safe_boundaries_cr1 : forall ad t,
    ~ value t ->
    safe_boundaries t ->
    safe_boundaries <{cr ad t}>

  | safe_boundaries_cr2 : forall ad t,
    value t ->
    safe_term t ->
    safe_boundaries <{cr ad t}>

  | safe_boundaries_spawn : forall t,
    safe_term t ->
    safe_boundaries <{spawn t}>
  .

