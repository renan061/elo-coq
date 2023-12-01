From Elo Require Import Core.
From Elo Require Import Definitions.
From Elo Require Import Inversions.

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

