From Elo Require Import Core.
From Elo Require Import Definitions.
From Elo Require Import Inversions.

(* ------------------------------------------------------------------------- *)
(* not-write-access constructors                                             *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_nwacc_construction :=
  intros ** ?; invc_wacc; contradiction.

Lemma nwacc_unit : forall m ad,
  ~ write_access ad m <{unit}>.
Proof.
  solve_nwacc_construction.
Qed.

Lemma nwacc_nat : forall m ad n,
  ~ write_access ad m <{nat n}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_fun : forall m x Tx t ad,
  ~ write_access ad m t ->
  ~ write_access ad m <{fn x Tx t}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_call : forall m t1 t2 ad,
  ~ write_access ad m t1 ->
  ~ write_access ad m t2 ->
  ~ write_access ad m <{call t1 t2}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_refS : forall m ad ad' T,
  ~ write_access ad m <{&ad' :: s&T}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_refX : forall m ad ad' T,
  ~ write_access ad m <{&ad' :: x&T}>.
Proof. solve_nwacc_construction. Qed.

(*
Lemma nacc_ref : forall m ad ad' T,
  ad <> ad' ->
  ~ access ad m m[ad'].tm ->
  ~ access ad m <{&ad' :: T}>.
Proof. solve_nacc_construction. Qed.
*)

Lemma nwacc_new : forall m t ad T,
  ~ write_access ad m t ->
  ~ write_access ad m <{new T t}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_load : forall m t ad,
  ~ write_access ad m t ->
  ~ write_access ad m <{*t}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_asg : forall m t1 t2 ad,
  ~ write_access ad m t1 ->
  ~ write_access ad m t2 ->
  ~ write_access ad m <{t1 = t2}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_acq : forall m t1 t2 ad,
  ~ write_access ad m t1 ->
  ~ write_access ad m t2 ->
  ~ write_access ad m <{acq t1 t2}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_cr : forall m t ad ad',
  ~ write_access ad m t ->
  ~ write_access ad m <{cr ad' t}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_ptm : forall m t ad tid,
  ~ write_access ad m t ->
  ~ write_access ad m <{ptm tid t}>.
Proof. solve_nwacc_construction. Qed.

Lemma nwacc_spawn : forall m t ad,
  ~ write_access ad m <{spawn t}>.
Proof. solve_nwacc_construction. Qed.

#[export] Hint Resolve
  nwacc_unit  nwacc_nat
  nwacc_fun   nwacc_call
  nwacc_refS  nwacc_refX
  nwacc_new   nwacc_load nwacc_asg
  nwacc_acq   nwacc_cr   nwacc_ptm
  nwacc_spawn
  : wacc.

(*
(* ------------------------------------------------------------------------- *)
(* not-access constructors                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_nacc_construction :=
  intros ** ?; invc_acc; contradiction.

Lemma nacc_unit : forall m ad,
  ~ access ad m <{unit}>.
Proof.
  intros ** ?. inv_acc.
Qed.

Lemma nacc_num : forall m ad n,
  ~ access ad m <{N n}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_ref : forall m ad ad' T,
  ad <> ad' ->
  ~ access ad m m[ad'].tm ->
  ~ access ad m <{&ad' :: T}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_new : forall m t ad T,
  ~ access ad m t ->
  ~ access ad m <{new T t}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_load : forall m t ad,
  ~ access ad m t ->
  ~ access ad m <{*t}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_asg : forall m t1 t2 ad,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{t1 = t2}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_fun : forall m x Tx t ad,
  ~ access ad m t ->
  ~ access ad m <{fn x Tx t}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_call : forall m t1 t2 ad,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{call t1 t2}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_seq : forall m t1 t2 ad,
  ~ access ad m t1 ->
  ~ access ad m t2 ->
  ~ access ad m <{t1; t2}>.
Proof. solve_nacc_construction. Qed.

Lemma nacc_spawn : forall m t ad,
  ~ access ad m <{spawn t}>.
Proof. solve_nacc_construction. Qed.

#[export] Hint Resolve
  nacc_unit nacc_num
  nacc_ref nacc_new nacc_load nacc_asg
  nacc_fun nacc_call
  nacc_seq
  nacc_spawn
  : acc.
*)
