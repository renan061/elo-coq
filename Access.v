From Elo Require Import Core.

From Elo Require Import ValidReferences.

(* ------------------------------------------------------------------------- *)
(* access                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Ignores <spawn> blocks. *)
Inductive access (ad : addr) (m : mem) : tm -> Prop :=
  | acc_fun : forall x Tx t,
    access ad m t ->
    access ad m <{fn x Tx t}>

  | acc_call1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{call t1 t2}>

  | acc_call2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{call t1 t2}>

  | acc_mem : forall ad' T,
    ad <> ad' ->
    access ad m m[ad'].t ->
    access ad m <{&ad' : T}>

  | acc_refR : forall T,
    access ad m <{&ad : r&T}>

  | acc_refW : forall T,
    access ad m <{&ad : w&T}>

  | acc_new : forall T t,
    access ad m t ->
    access ad m <{new t : T}>

  | acc_load : forall t,
    access ad m t ->
    access ad m <{*t}>

  | acc_asg1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{t1 := t2}>

  | acc_asg2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{t1 := t2}>

  | acc_acq1 : forall t1 t2,
    access ad m t1 ->
    access ad m <{acq t1 t2}>

  | acc_acq2 : forall t1 t2,
    access ad m t2 ->
    access ad m <{acq t1 t2}>

  | acc_cr : forall ad' t,
    access ad m t ->
    access ad m <{cr ad' t}>
  .

(* ------------------------------------------------------------------------- *)
(* guards                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition guards adX ad m :=
  exists T, m[adX].T = `x&T` /\ access ad m m[adX].t.

Notation "adX `guards` ad `in` m" := (guards adX ad m)
  (at level 70, ad at next level).

(* ------------------------------------------------------------------------- *)
(* critical-access                                                           *)
(* ------------------------------------------------------------------------- *)

Inductive critical_access (ad adX : addr) (m : mem) : tm -> Prop :=
  | cacc_fun : forall x Tx t,
    critical_access ad adX m t ->
    critical_access ad adX m <{fn x Tx t}>

  | cacc_call1 : forall t1 t2,
    critical_access ad adX m t1 ->
    critical_access ad adX m <{call t1 t2}>

  | cacc_call2 : forall t1 t2,
    critical_access ad adX m t2 ->
    critical_access ad adX m <{call t1 t2}>

  | cacc_new : forall T t,
    critical_access ad adX m t ->
    critical_access ad adX m <{new t : T}>

  | cacc_load : forall t,
    critical_access ad adX m t ->
    critical_access ad adX m <{*t}>

  | cacc_asg1 : forall t1 t2,
    critical_access ad adX m t1 ->
    critical_access ad adX m <{t1 := t2}>

  | cacc_asg2 : forall t1 t2,
    critical_access ad adX m t2 ->
    critical_access ad adX m <{t1 := t2}>

  | cacc_acq1 : forall t1 t2,
    critical_access ad adX m t1 ->
    critical_access ad adX m <{acq t1 t2}>

  | cacc_acq2 : forall t1 t2,
    critical_access ad adX m t2 ->
    critical_access ad adX m <{acq t1 t2}>

  | cacc_cr_eq : forall t,
    access ad m t ->
    critical_access ad adX m <{cr adX t}>

  | cacc_cr_neq : forall adX' t,
    adX <> adX' ->
    critical_access ad adX m t ->
    critical_access ad adX m <{cr adX' t}>
  .

(* ------------------------------------------------------------------------- *)
(* write-access                                                              *)
(* ------------------------------------------------------------------------- *)

(* Access through a "write" reference. *)
Inductive write_access (ad : addr) (m : mem) : tm  -> Prop :=
  | wacc_fun : forall x Tx t,
    write_access ad m t ->
    write_access ad m <{fn x Tx t}>

  | wacc_call1 : forall t1 t2,
    write_access ad m t1 ->
    write_access ad m <{call t1 t2}>

  | wacc_call2 : forall t1 t2,
    write_access ad m t2 ->
    write_access ad m <{call t1 t2}>

  | wacc_mem : forall ad' T,
    ad <> ad' ->
    write_access ad m (m[ad'].t) ->
    write_access ad m <{&ad' : w&T}>

  | wacc_ref : forall T,
    write_access ad m <{&ad : w&T}>

  | wacc_new : forall T t,
    write_access ad m t ->
    write_access ad m <{new t : T}>

  | wacc_load : forall t,
    write_access ad m t ->
    write_access ad m <{*t}>

  | wacc_asg1 : forall t1 t2,
    write_access ad m t1 ->
    write_access ad m <{t1 := t2}>

  | wacc_asg2 : forall t1 t2,
    write_access ad m t2 ->
    write_access ad m <{t1 := t2}>

  | wacc_acq1 : forall t1 t2,
    write_access ad m t1 ->
    write_access ad m <{acq t1 t2}>

  | wacc_acq2 : forall t1 t2,
    write_access ad m t2 ->
    write_access ad m <{acq t1 t2}>

  | wacc_cr : forall ad' t,
    write_access ad m t ->
    write_access ad m <{cr ad' t}>
  .

(* ------------------------------------------------------------------------- *)
(* read-access                                                               *)
(* ------------------------------------------------------------------------- *)

Definition read_access ad m t := access ad m t /\ ~ write_access ad m t.

(* ------------------------------------------------------------------------- *)
(* inversions                                                                *)
(* ------------------------------------------------------------------------- *)

Local Ltac _accs P tt :=
  match goal with
  | H : P _ _ <{unit     }>   |- _ => tt H
  | H : P _ _ <{nat _    }>   |- _ => tt H
  | H : P _ _ <{var _    }>   |- _ => tt H
  | H : P _ _ <{fn _ _ _ }>   |- _ => tt H
  | H : P _ _ <{call _ _ }>   |- _ => tt H
  | H : P _ _ <{& _ : _  }>   |- _ => tt H
  | H : P _ _ <{new _ : _}>   |- _ => tt H
  | H : P _ _ <{* _      }>   |- _ => tt H
  | H : P _ _ <{_ := _   }>   |- _ => tt H
  | H : P _ _ <{acq _  _ }>   |- _ => tt H
  | H : P _ _ <{cr _ _   }>   |- _ => tt H
  | H : P _ _ <{spawn _  }>   |- _ => tt H
  end.

Ltac inv_acc  := _accs access inv.
Ltac invc_acc := _accs access invc.

Ltac inv_wacc  := _accs write_access invc.
Ltac invc_wacc := _accs write_access invc.
