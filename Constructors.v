From Elo Require Import Core.
From Elo Require Import Definitions.
From Elo Require Import Inversions.

(* ------------------------------------------------------------------------- *)
(* valid-addresses construction                                              *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vad_construction := 
  intros ** ? ?; inv_hasad; eauto.

Local Lemma vad_unit : forall m,
  valid_addresses m <{unit}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_num : forall m n,
  valid_addresses m <{N n}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_ad : forall m ad T,
  ad < #m ->
  valid_addresses m <{&ad :: T}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_new : forall m t T,
  valid_addresses m t ->
  valid_addresses m <{new T t}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_load : forall m t,
  valid_addresses m t ->
  valid_addresses m <{*t}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_asg : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{t1 = t2}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_var : forall m x,
  valid_addresses m <{var x}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_fun : forall m x Tx t,
  valid_addresses m t ->
  valid_addresses m <{fn x Tx t}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_call : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{call t1 t2}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_seq : forall m t1 t2,
  valid_addresses m t1 ->
  valid_addresses m t2 ->
  valid_addresses m <{t1; t2}>.
Proof. solve_vad_construction. Qed.

Local Lemma vad_spawn : forall m t,
  valid_addresses m t ->
  valid_addresses m <{spawn t}>.
Proof. solve_vad_construction. Qed.

#[export] Hint Resolve
  vad_unit vad_num
  vad_ad vad_new vad_load vad_asg
  vad_var vad_fun vad_call vad_seq vad_spawn
  : vad.

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

