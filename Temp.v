
(* preservation lemmas ----------------------------------------------------- *)

Local Lemma nacc_subst : forall ad m x tx t,
  consistent_inits m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad m tx ->
  ~ access ad m <{[x := tx] t}>.
Proof.
  intros * ? Ht Htx.
  induction t; trivial; simpl in *; invc_ci; invc_nacc;
  try destruct str_eq_dec; eauto with not_access.
Qed.

Local Lemma nacc_mem_set1 : forall m t ad ad' t',
  ~ access ad m t' ->
  ~ access ad m t  ->
  ~ access ad m[ad'.t <- t'] t.
Proof.
  intros ** Hacc. induction Hacc; eauto using access;
  repeat omicron; invc_nacc; eauto; upsilon; exfalso; eauto.
Qed.

(*
Local Lemma nacc_mem_set2 : forall m t ad ad' c,
  ~ access ad' m t ->
  ~ access ad  m t ->
  ~ access ad  m[ad' <- c] t.
Proof.
  intros ** Hacc.
  induction Hacc; invc_nacc; eauto using access; sigma; eauto.
  - exfalso. invc_nacc.
    + invc_nacc; eauto.
      * eauto.
  upsilon.
Qed.
*)






(* ------------------------------------------------------------------------- *)
(* write-access                                                              *)
(* ------------------------------------------------------------------------- *)

(* Access through a "write" reference. *)
Inductive write_access (ad : addr) (m : mem) : tm  -> Prop :=
  | wacc_fun   : forall x Tx t, write_access ad m t  ->
                                write_access ad m <{fn x Tx t }>

  | wacc_call1 : forall t1 t2,  write_access ad m t1 ->
                                write_access ad m <{call t1 t2}>

  | wacc_call2 : forall t1 t2,  write_access ad m t2 ->
                                write_access ad m <{call t1 t2}>

  | wacc_mem   : forall ad' T,  ad <> ad'                  ->
                                write_access ad m m[ad'].t ->
                                write_access ad m <{&ad' : w&T}>

  | wacc_ref   :  forall T,     write_access ad m <{&ad  : w&T}>

  | wacc_new   : forall T t,    write_access ad m t  ->
                                write_access ad m <{new t : T }>

  | wacc_load  : forall t,      write_access ad m t  ->
                                write_access ad m <{*t        }>

  | wacc_asg1  : forall t1 t2,  write_access ad m t1 ->
                                write_access ad m <{t1 := t2  }>

  | wacc_asg2  : forall t1 t2,  write_access ad m t2 ->
                                write_access ad m <{t1 := t2  }>

  | wacc_acq1  : forall t1 t2,  write_access ad m t1 ->
                                write_access ad m <{acq t1 t2 }>

  | wacc_acq2  : forall t1 t2,  write_access ad m t2 ->
                                write_access ad m <{acq t1 t2 }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _wacc tt :=
  match goal with
  | H : write_access _ _ <{unit     }>   |- _ => inv H
  | H : write_access _ _ <{nat _    }>   |- _ => inv H
  | H : write_access _ _ <{var _    }>   |- _ => inv H
  | H : write_access _ _ <{fn _ _ _ }>   |- _ => tt H
  | H : write_access _ _ <{call _ _ }>   |- _ => tt H
  | H : write_access _ _ <{& _ : _  }>   |- _ => tt H
  | H : write_access _ _ <{new _ : _}>   |- _ => tt H
  | H : write_access _ _ <{* _      }>   |- _ => tt H
  | H : write_access _ _ <{_ := _   }>   |- _ => tt H
  | H : write_access _ _ <{acq _  _ }>   |- _ => tt H
  | H : write_access _ _ <{cr _ _   }>   |- _ => inv H
  | H : write_access _ _ <{spawn _  }>   |- _ => inv H
  end.

Ltac inv_wacc  := _wacc inv.
Ltac invc_wacc := _wacc invc.

(* ------------------------------------------------------------------------- *)
(* read-access                                                              *)
(* ------------------------------------------------------------------------- *)

Definition read_access (ad : addr) (m : mem) (t : tm) :=
  access ad m t /\ ~ write_access ad m t.

(* ------------------------------------------------------------------------- *)
(* not-write-access                                                          *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_inv_nwacc := 
  intros; try split; eauto using write_access.

Local Lemma inv_nwacc_fun : forall m x Tx t ad,
  ~ write_access ad m <{fn x Tx t}> -> ~ write_access  ad m t.
Proof. solve_inv_nwacc. Qed.

Local Lemma inv_nwacc_call : forall m t1 t2 ad,
  ~ write_access ad m <{call t1 t2}> ->
  ~ write_access ad m t1 /\ ~ write_access ad m t2.
Proof. solve_inv_nwacc. Qed.

Local Lemma inv_nwacc_ref : forall m ad ad' T,
  ~ write_access ad m <{&ad' : `w&T`}> ->
  ad <> ad' /\ ~ write_access ad m m[ad'].t.
Proof.
  intros. assert (ad <> ad') by (intros ?; subst; eauto using write_access).
  split; eauto using write_access.
Qed.

Local Lemma inv_nwacc_new : forall m t ad T,
  ~ write_access ad m <{new t : T}> -> ~ write_access ad m t.
Proof. solve_inv_nwacc. Qed.

Local Lemma inv_nwacc_load : forall m t ad,
  ~ write_access ad m <{*t}> -> ~ write_access ad m t.
Proof. solve_inv_nwacc. Qed.

Local Lemma inv_nwacc_asg : forall m t1 t2 ad,
  ~ write_access ad m <{t1 := t2}> ->
  ~ write_access ad m t1 /\ ~ write_access ad m t2.
Proof. solve_inv_nwacc. Qed.

Local Lemma inv_nwacc_acq : forall m t1 t2 ad,
  ~ write_access ad m <{acq t1 t2}> ->
  ~ write_access ad m t1 /\ ~ write_access ad m t2.
Proof. solve_inv_nwacc. Qed.

Ltac invc_nwacc :=
  match goal with
  | H : ~ write_access _ _ <{unit       }> |- _ => clear H
  | H : ~ write_access _ _ <{nat _      }> |- _ => clear H
  | H : ~ write_access _ _ <{var _      }> |- _ => clear H
  | H : ~ write_access _ _ <{fn _ _ _   }> |- _ => eapply inv_nwacc_fun  in H
  | H : ~ write_access _ _ <{call _ _   }> |- _ => eapply inv_nwacc_call in H
                                                                     as [? ?]
  | H : ~ write_access _ _ <{& _ : `r&_`}> |- _ => clear H
  | H : ~ write_access _ _ <{& _ : `x&_`}> |- _ => clear H
  | H : ~ write_access _ _ <{& _ : `w&_`}> |- _ => eapply inv_nwacc_ref in H
                                                                     as [? ?]
  | H : ~ write_access _ _ <{new _ : _  }> |- _ => eapply inv_nwacc_new  in H
  | H : ~ write_access _ _ <{* _        }> |- _ => eapply inv_nwacc_load in H
  | H : ~ write_access _ _ <{_ := _     }> |- _ => eapply inv_nwacc_asg  in H
                                                                     as [? ?]
  | H : ~ write_access _ _ <{acq _ _    }> |- _ => eapply inv_nwacc_acq  in H
                                                                     as [? ?]
  | H : ~ write_access _ _ <{cr _ _     }> |- _ => clear H
  | H : ~ write_access _ _ <{spawn _    }> |- _ => clear H
  end.

(* ------------------------------------------------------------------------- *)
(* basic lemmas                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma wacc_then_acc : forall ad m t,
  write_access ad m t ->
  access ad m t.
Proof.
  intros * Hwacc. induction Hwacc; eauto using access.
Qed.

Lemma racc_then_acc : forall ad m t,
  read_access ad m t ->
  access ad m t.
Proof.
  intros * [? _]. assumption.
Qed.

Lemma safe_then_nwacc : forall m ad ad' T,
  forall_memory m value ->
  empty |-- m[ad'].t is `Safe T` ->
  ~ write_access ad m m[ad'].t.
Proof.
  intros * Hval **. intros ?.
  destruct (Hval ad'); invc_typeof; invc_wacc; eauto.
Qed.

