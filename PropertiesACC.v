From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
From Elo Require Import Core.
From Elo Require Import CoreExt.

From Elo Require Import Definitions.

From Elo Require Import PropertiesVAD.


(* ------------------------------------------------------------------------- *)
(* misc. properties                                                          *)
(* ------------------------------------------------------------------------- *)

(* TODO: rename and ask Roberto about that test scrambling thing. *)
Theorem acc_from_mem_set : forall m t ad ad' vT,
  ~ access ad m t ->
  access ad m[ad' <- vT] t ->
  access ad' m t.
Proof.
  intros. induction t; inv_acc; inv_nacc; eauto using access.
  match goal with |- access _ _ <{&?ad :: _}> => rename ad into ad'' end.
  destruct (nat_eq_dec ad' ad''); subst; eauto using access.
  simpl_array. eapply acc_mem; trivial.
  destruct (acc_dec ad' m m[ad''].tm); trivial. exfalso.
  eapply (alt_nacc_mem_set_preservation _ _ ad ad'); eauto.
Qed.

