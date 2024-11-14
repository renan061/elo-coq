From Elo Require Import Core.

From Elo Require Import Properties.

(* ------------------------------------------------------------------------- *)
(* access                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Ignores monitor initializers, critical regions, and spawn blocks. *)
Inductive access (ad : addr) (m : mem) : tm -> Prop :=
  | acc_fun   : forall x Tx t,  access ad m t  ->
                                access ad m <{fn x Tx t       }>

  | acc_call1 : forall t1 t2,   access ad m t1 ->
                                access ad m <{call t1 t2      }>

  | acc_call2 : forall t1 t2,   access ad m t2 ->
                                access ad m <{call t1 t2      }>

  | acc_memR  : forall t ad' T, ad <> ad'         ->
                                m[ad'].t = Some t ->
                                access ad m t     ->
                                access ad m <{&ad' : r&T      }>

  | acc_memW  : forall t ad' T, ad <> ad'         ->
                                m[ad'].t = Some t ->
                                access ad m t     ->
                                access ad m <{&ad' : w&T      }>

  | acc_refR  : forall T,       access ad m <{&ad  : r&T      }>

  | acc_refW  : forall T,       access ad m <{&ad  : w&T      }>

  | acc_new   : forall t T,     access ad m t  ->
                                access ad m <{new t : T       }>

  | acc_initR : forall ad' t T, access ad m t  ->
                                access ad m <{init ad' t : r&T}>

  | acc_initW : forall ad' t T, access ad m t  ->
                                access ad m <{init ad' t : w&T}>

  | acc_load  : forall t,       access ad m t  ->
                                access ad m <{*t              }>

  | acc_asg1  : forall t1 t2,   access ad m t1 ->
                                access ad m <{t1 := t2        }>

  | acc_asg2  : forall t1 t2,   access ad m t2 ->
                                access ad m <{t1 := t2        }>

  | acc_acq1  : forall t1 t2,   access ad m t1 ->
                                access ad m <{acq t1 t2       }>

  | acc_acq2  : forall t1 t2,   access ad m t2 ->
                                access ad m <{acq t1 t2       }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _acc tt :=
  match goal with
  | H : access _ _ <{unit          }>   |- _ => inv H
  | H : access _ _ <{nat _         }>   |- _ => inv H
  | H : access _ _ <{var _         }>   |- _ => inv H
  | H : access _ _ <{fn _ _ _      }>   |- _ => tt H
  | H : access _ _ <{call _ _      }>   |- _ => tt H
  | H : access _ _ <{& _ : _       }>   |- _ => tt H
  | H : access _ _ <{new _ : _     }>   |- _ => tt H
  | H : access _ _ <{init _ _ : _  }>   |- _ => tt H
  | H : access _ _ <{* _           }>   |- _ => tt H
  | H : access _ _ <{_ := _        }>   |- _ => tt H
  | H : access _ _ <{acq _  _      }>   |- _ => tt H
  | H : access _ _ <{cr _ _        }>   |- _ => inv H
  | H : access _ _ <{spawn _       }>   |- _ => inv H
  end.

Ltac inv_acc  := _acc inv.
Ltac invc_acc := _acc invc.

(* ------------------------------------------------------------------------- *)
(* xaccess                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Access through monitor initializers and critical regions. *)
Inductive xaccess (adx ad : addr) (m : mem) : tm -> Prop :=
  | xacc_fun       : forall x Tx t,   xaccess adx ad m t  ->
                                      xaccess adx ad m <{fn x Tx t        }>

  | xacc_call1     : forall t1 t2,    xaccess adx ad m t1 ->
                                      xaccess adx ad m <{call t1 t2       }>

  | xacc_call2     : forall t1 t2,    xaccess adx ad m t2 ->
                                      xaccess adx ad m <{call t1 t2       }>

  | xacc_new       : forall t T,      xaccess adx ad m t  ->
                                      xaccess adx ad m <{new t : T        }>

  | xacc_initR     : forall adx' t T, xaccess adx ad m t  ->
                                      xaccess adx ad m <{init adx' t : r&T}>

  | xacc_initX_eq  : forall t T,      access ad m t       ->
                                      xaccess adx ad m <{init adx  t : x&T}>

  | xacc_initX_neq : forall adx' t T, adx <> adx'         ->
                                      xaccess adx ad m t  ->
                                      xaccess adx ad m <{init adx' t : x&T}>

  | xacc_initW     : forall adx' t T, xaccess adx ad m t  ->
                                      xaccess adx ad m <{init adx' t : w&T}>

  | xacc_load      : forall t,        xaccess adx ad m t  ->
                                      xaccess adx ad m <{*t               }>

  | xacc_asg1      : forall t1 t2,    xaccess adx ad m t1 ->
                                      xaccess adx ad m <{t1 := t2         }>

  | xacc_asg2      : forall t1 t2,    xaccess adx ad m t2 ->
                                      xaccess adx ad m <{t1 := t2         }>

  | xacc_acq1      : forall t1 t2,    xaccess adx ad m t1 ->
                                      xaccess adx ad m <{acq t1 t2        }>

  | xacc_acq2      : forall t1 t2,    xaccess adx ad m t2 ->
                                      xaccess adx ad m <{acq t1 t2        }>

  | xacc_cr_eq     : forall t,        access ad m t       ->
                                      xaccess adx ad m <{cr adx t         }>

  | xacc_cr_neq    : forall adx' t,   adx <> adx'         ->
                                      xaccess adx ad m t  ->
                                      xaccess adx ad m <{cr adx' t        }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _xacc tt :=
  match goal with
  | H : xaccess _ _ _ <{unit        }>   |- _ => inv H
  | H : xaccess _ _ _ <{nat _       }>   |- _ => inv H
  | H : xaccess _ _ _ <{var _       }>   |- _ => inv H
  | H : xaccess _ _ _ <{fn _ _ _    }>   |- _ => tt H
  | H : xaccess _ _ _ <{call _ _    }>   |- _ => tt H
  | H : xaccess _ _ _ <{& _ : _     }>   |- _ => inv H
  | H : xaccess _ _ _ <{new _ : _   }>   |- _ => tt H
  | H : xaccess _ _ _ <{init _ _ : _}>   |- _ => tt H
  | H : xaccess _ _ _ <{* _         }>   |- _ => tt H
  | H : xaccess _ _ _ <{_ := _      }>   |- _ => tt H
  | H : xaccess _ _ _ <{acq _  _    }>   |- _ => tt H
  | H : xaccess _ _ _ <{cr _ _      }>   |- _ => tt H
  | H : xaccess _ _ _ <{spawn _     }>   |- _ => inv H
  end.

Ltac inv_xacc  := _xacc inv.
Ltac invc_xacc := _xacc invc.

