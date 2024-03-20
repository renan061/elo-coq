From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* valid-addresses                                                           *)
(* ------------------------------------------------------------------------- *)

(* Addresses are valid if they are within the bounds of the memory. *)
Inductive valid_addresses (m : mem) : tm -> Prop :=
  | vad_unit :
    valid_addresses m <{unit}>

  | vad_num : forall n,
    valid_addresses m <{N n}>

  | vad_ref : forall ad T,
    ad < #m ->
    valid_addresses m <{&ad :: T}>

  | vad_new : forall t T,
    valid_addresses m t ->
    valid_addresses m <{new T t}>

  | vad_load : forall t,
    valid_addresses m t ->
    valid_addresses m <{*t}>

  | vad_asg : forall t1 t2,
    valid_addresses m t1 ->
    valid_addresses m t2 ->
    valid_addresses m <{t1 = t2}>

  | vad_seq : forall t1 t2,
    valid_addresses m t1 ->
    valid_addresses m t2 ->
    valid_addresses m <{t1; t2}>

  | vad_var : forall x,
    valid_addresses m <{var x}>

  | vad_fun : forall x T t,
    valid_addresses m t ->
    valid_addresses m <{fn x T t}>

  | vad_call : forall t1 t2,
    valid_addresses m t1 ->
    valid_addresses m t2 ->
    valid_addresses m <{call t1 t2}>

  | vad_spawn : forall t,
    valid_addresses m t ->
    valid_addresses m <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* well-typed-term                                                           *)
(* ------------------------------------------------------------------------- *)

Definition well_typed_term (t : tm) :=
  exists T, empty |-- t is T.

(* ------------------------------------------------------------------------- *)
(* consistently-typed-references                                             *)
(* ------------------------------------------------------------------------- *)

Inductive consistently_typed_references (m : mem) : tm -> Prop :=
  | ctr_unit :
    consistently_typed_references m <{unit}> 

  | ctr_num : forall n,
    consistently_typed_references m <{N n}>

  | ctr_refM : forall T ad,
    empty |-- m[ad].tm is T ->
    m[ad].typ = <{{ &T }}> ->
    consistently_typed_references m <{&ad :: &T}>

  | ctr_refI : forall T ad,
    empty |-- m[ad].tm is <{{ Immut T }}> ->
    m[ad].typ = <{{ i&T }}> ->
    consistently_typed_references m <{&ad :: i&T}>

  | ctr_new : forall T t,
    consistently_typed_references m t ->
    consistently_typed_references m <{new T t}> 

  | ctr_load : forall t,
    consistently_typed_references m t ->
    consistently_typed_references m <{*t}> 

  | ctr_asg : forall t1 t2,
    consistently_typed_references m t1 ->
    consistently_typed_references m t2 ->
    consistently_typed_references m <{t1 = t2}> 

  | ctr_var : forall x,
    consistently_typed_references m <{var x}>

  | ctr_fun : forall x Tx t,
    consistently_typed_references m t ->
    consistently_typed_references m <{fn x Tx t}>

  | ctr_call : forall t1 t2,
    consistently_typed_references m t1 ->
    consistently_typed_references m t2 ->
    consistently_typed_references m <{call t1 t2}> 

  | ctr_seq : forall t1 t2,
    consistently_typed_references m t1 ->
    consistently_typed_references m t2 ->
    consistently_typed_references m <{t1; t2}>

  | ctr_spawn : forall t,
    consistently_typed_references m t ->
    consistently_typed_references m <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* access                                                                    *)
(* ------------------------------------------------------------------------- *)

(*
  A term has access to an address if it refers to the address directly or 
  indirectly.
  
  Ignores <spawn> blocks.
*)
Inductive access (ad : addr) (m : mem) : tm -> Prop :=
  | acc_mem : forall ad' T,
    ad <> ad' ->
    access ad m m[ad'].tm ->
    access ad m <{&ad' :: T}>

  | acc_ref : forall T,
    access ad m <{&ad :: T}>

  | acc_new : forall T t,
    access ad m t ->
    access ad m <{new T t}>

  | acc_load : forall t,
    access ad m t ->
    access ad m <{*t}>

  | acc_asg1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{t1 = t2}>

  | acc_asg2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{t1 = t2}>

  | acc_fun : forall x Tx t,
    access ad m t ->
    access ad m <{fn x Tx t}>

  | acc_call1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{call t1 t2}>

  | acc_call2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{call t1 t2}>

  | acc_seq1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{t1; t2}>

  | acc_seq2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{t1; t2}>
  .

(* ------------------------------------------------------------------------- *)
(* unsafe-access                                                             *)
(* ------------------------------------------------------------------------- *)

(* There is a mutable pointer to <ad> in the term. *)
Inductive unsafe_access (ad : addr) (m : mem) : tm  -> Prop :=
  | uacc_mem : forall ad' T,
    ad <> ad' ->
    unsafe_access ad m (m[ad'].tm) ->
    unsafe_access ad m <{&ad' :: &T}>

  | uacc_ref : forall T,
    unsafe_access ad m <{&ad :: &T}>

  | uacc_new : forall T t,
    unsafe_access ad m t ->
    unsafe_access ad m <{new T t}>

  | uacc_load : forall t,
    unsafe_access ad m t ->
    unsafe_access ad m <{*t}>

  | uacc_asg1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{t1 = t2}>

  | uacc_asg2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{t1 = t2}>

  | uacc_fun : forall x Tx t,
    unsafe_access ad m t ->
    unsafe_access ad m <{fn x Tx t}>

  | uacc_call1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{call t1 t2}>

  | uacc_call2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{call t1 t2}>

  | uacc_seq1 : forall t1 t2,
    unsafe_access ad m t1 ->
    unsafe_access ad m <{t1; t2}>

  | uacc_seq2 : forall t1 t2,
    unsafe_access ad m t2 ->
    unsafe_access ad m <{t1; t2}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-access                                                               *)
(* ------------------------------------------------------------------------- *)

Definition safe_access ad m t := access ad m t /\ ~ unsafe_access ad m t.

(* ------------------------------------------------------------------------- *)
(* no-mut                                                                    *)
(* ------------------------------------------------------------------------- *)

(* A term is no-mut if it has no mutable references. *)
Inductive no_mut : tm -> Prop :=
  | nomut_unit :
    no_mut <{unit}>

  | nomut_num : forall n,
    no_mut <{N n}>

  | nomut_ref : forall ad T,
    no_mut <{&ad :: i&T}>

  | nomut_new : forall T t,
    no_mut t ->
    no_mut <{new T t}>

  | nomut_load : forall t,
    no_mut t ->
    no_mut <{*t}>

  | nomut_asg : forall t1 t2,
    no_mut t1 ->
    no_mut t2 ->
    no_mut <{t1 = t2}>

  | nomut_var : forall x,
    no_mut <{var x}>

  | nomut_fun : forall x Tx t,
    no_mut t ->
    no_mut <{fn x Tx t}>

  | nomut_call : forall t1 t2,
    no_mut t1 ->
    no_mut t2 ->
    no_mut <{call t1 t2}>

  | nomut_seq : forall t1 t2,
    no_mut t1 ->
    no_mut t2 ->
    no_mut <{t1; t2}>

  | nomut_spawn : forall t,
    no_mut t ->
    no_mut <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-spawns                                                               *)
(* ------------------------------------------------------------------------- *)

(* A term has safe spawns if all of its spawns have no mutable references. *)
Inductive safe_spawns : tm -> Prop :=
  | ss_unit :
      safe_spawns <{unit}>

  | ss_num : forall n,
      safe_spawns <{N n}>

  | ss_ref : forall ad T,
      safe_spawns <{&ad :: T}>

  | ss_new : forall T t,
      safe_spawns t ->
      safe_spawns <{new T t}>

  | ss_load : forall t,
      safe_spawns t ->
      safe_spawns <{*t}>

  | ss_asg : forall t1 t2,
      safe_spawns t1 ->
      safe_spawns t2 ->
      safe_spawns <{t1 = t2}>

  | ss_var : forall x,
      safe_spawns <{var x}>

  | ss_fun : forall x Tx t,
      safe_spawns t ->
      safe_spawns <{fn x Tx t}>

  | ss_call : forall t1 t2,
      safe_spawns t1 ->
      safe_spawns t2 ->
      safe_spawns <{call t1 t2}>

  | ss_seq : forall t1 t2,
      safe_spawns t1 ->
      safe_spawns t2 ->
      safe_spawns <{t1; t2}>

  | ss_spawn : forall t,
      no_mut t ->
      safe_spawns <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* has-var                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive has_var (x : id) : tm  -> Prop :=
  | hv_new : forall T t,
    has_var x t ->
    has_var x <{new T t}>

  | hv_load : forall t,
    has_var x t ->
    has_var x <{*t}>

  | hv_asg1 : forall t1 t2,
    has_var x t1 ->
    has_var x <{t1 = t2}>

  | hv_asg2 : forall t1 t2,
    has_var x t2 ->
    has_var x <{t1 = t2}>

  | hv_var :
    has_var x <{var x}>

  | hv_fun : forall x' Tx t,
    x <> x' ->
    has_var x t ->
    has_var x <{fn x' Tx t}>

  | hv_call1 : forall t1 t2,
    has_var x t1 ->
    has_var x <{call t1 t2}>

  | hv_call2 : forall t1 t2,
    has_var x t2 ->
    has_var x <{call t1 t2}>

  | hv_seq1 : forall t1 t2,
    has_var x t1 ->
    has_var x <{t1; t2}>

  | hv_seq2 : forall t1 t2,
    has_var x t2 ->
    has_var x <{t1; t2}>

  | hv_spawn : forall t,
    has_var x t ->
    has_var x <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-memory-sharing                                                       *)
(* ------------------------------------------------------------------------- *)

Definition safe_memory_sharing m ths := forall tid1 tid2 ad,
  tid1 <> tid2 ->
  access ad m ths[tid2] ->
  ~ unsafe_access ad m ths[tid1].

(* ------------------------------------------------------------------------- *)
(* sugars                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition not_access ad m t := ~ access ad m t.

Definition not_unsafe_access ad m t := ~ unsafe_access ad m t.

