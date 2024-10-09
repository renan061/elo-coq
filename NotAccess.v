

(* ------------------------------------------------------------------------- *)
(* not-write-access inversion                                                *)
(* ------------------------------------------------------------------------- *)

Local Lemma inv_nwacc_ref_eq : forall m ad T,
  ~ write_access ad m <{&ad : w&T}> ->
  False.
Proof. eauto using write_access. Qed.

Local Lemma inv_nuacc_ref_neqW : forall m ad ad' T,
  ~ write_access ad m <{&ad' : w&T}> ->
  (ad <> ad' /\ ~ write_access ad m m[ad'].t).
Proof.
  intros. destruct (nat_eq_dec ad ad'); subst; eauto using write_access.
  exfalso. eauto using inv_nwacc_ref_eq.
Qed.

Lemma inv_nuacc_ref_neqI : forall m ad ad' T,
  forall_memory m value ->
  valid_references m <{&ad' : r&T}> ->
  (* --- *)
  ~ write_access ad m <{&ad' : r&T}> ->
  ~ write_access ad m m[ad'].t.
Proof.
  intros * Hval **. invc_vr. intros ?.
  specialize (Hval ad'); simpl in *.
  destruct Hval; inv_typeof; inv_wacc; eauto.
Qed.

Local Ltac solve_nuacc_inversion :=
  intros; try (split; intros); eauto using write_access.

Local Ltac solve_nwacc_inversion :=
  intros; try (split; intros); eauto using write_access.

Local Lemma inv_nwacc_fun : forall m t ad x Tx,
  ~ write_access ad m <{fn x Tx t}> ->
  ~ write_access ad m t.
Proof. solve_nwacc_inversion. Qed.

Local Lemma inv_nwacc_call : forall m t1 t2 ad,
  ~ write_access ad m <{call t1 t2}> ->
  ~ write_access ad m t1 /\ ~ write_access ad m t2.
Proof. solve_nwacc_inversion. Qed.

Local Lemma inv_nwacc_ref : forall m ad T,
  ~ write_access ad m <{&ad :: u&T}> ->
  False.
Proof. solve_nwacc_inversion. Qed.

Local Lemma inv_nwacc_new : forall m t ad T,
  ~ write_access ad m <{new T t}> ->
  ~ write_access ad m t.
Proof. solve_nwacc_inversion. Qed.

Local Lemma inv_nwacc_load : forall m t ad,
  ~ write_access ad m <{*t}> ->
  ~ write_access ad m t.
Proof. solve_nwacc_inversion. Qed.

Local Lemma inv_nwacc_asg : forall m t1 t2 ad,
  ~ write_access ad m <{t1 = t2}> ->
  ~ write_access ad m t1 /\ ~ write_access ad m t2.
Proof. solve_nwacc_inversion. Qed.

Local Lemma inv_nwacc_acq : forall m t1 t2 ad,
  ~ write_access ad m <{acq t1 t2}> ->
  ~ write_access ad m t1 /\ ~ write_access ad m t2.
Proof. solve_nwacc_inversion. Qed.

Local Lemma inv_nwacc_cr : forall m t ad ad',
  ~ write_access ad m <{cr ad' t}> ->
  ~ write_access ad m t.
Proof. solve_nwacc_inversion. Qed.

Local Lemma inv_nwacc_ptm : forall m t ad tid,
  ~ write_access ad m <{ptm tid t}> ->
  ~ write_access ad m t.
Proof. solve_nwacc_inversion. Qed.

Local Notation wacc := (write_access).

Ltac inv_nwacc :=
  match goal with
  | H : ~ wacc _ _ <{unit    }> |- _ => clear H
  | H : ~ wacc _ _ <{nat _   }> |- _ => clear H
  | H : ~ wacc _ _ <{var _   }> |- _ => clear H
  | H : ~ wacc _ _ <{fn _ _ _}> |- _ => eapply inv_nwacc_fun  in H
  | H : ~ wacc _ _ <{call _ _}> |- _ => eapply inv_nwacc_call in H as [? ?]
  | H : ~ wacc _ _ <{new _ _ }> |- _ => eapply inv_nwacc_new  in H
  | H : ~ wacc _ _ <{* _     }> |- _ => eapply inv_nwacc_load in H
  | H : ~ wacc _ _ <{_ = _   }> |- _ => eapply inv_nwacc_asg  in H as [? ?]
  | H : ~ wacc _ _ <{acq _ _ }> |- _ => eapply inv_nwacc_acq  in H as [? ?]
  | H : ~ wacc _ _ <{cr _ _  }> |- _ => eapply inv_nwacc_cr   in H
  | H : ~ wacc _ _ <{ptm _ _ }> |- _ => eapply inv_nwacc_ptm  in H

  | H : ~ wacc ?ad _ <{& ?ad :: u&_}>   |- _ => eapply inv_nwacc_ref in H;
                                                solve contradiction
  end.

Ltac inv_nuacc :=
  match goal with
  | H : ~ write_access ?ad _ <{& ?ad  :: & _ }> |- _ =>
    eapply inv_nuacc_ref_eq   in H; solve contradiction
  | H : ~ write_access ?ad _ <{& ?ad' :: & _ }> |- _ =>
    eapply inv_nuacc_ref_neqM in H as [? ?]
  | H : ~ write_access _ _   <{new _ _       }> |- _ =>

  | Hval   : forall_memory ?m value,
    Hctr   : consistently_typed_references ?m <{& ?ad' :: (i& ?T) }>,
    Hnuacc : ~ write_access ?ad ?m <{& ?ad' :: (i& ?T) }> |- _ =>
    eapply (inv_nuacc_ref_neqI m ad ad' T Hval Hctr) in Hnuacc
  end.

