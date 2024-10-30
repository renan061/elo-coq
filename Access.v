From Elo Require Import Core.

From Elo Require Import WellTypedTerm.
From Elo Require Import ValidReferences.
From Elo Require Import Boundaries.

(* ------------------------------------------------------------------------- *)
(* access                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Ignores <spawn> blocks and critical regions. *)
Inductive access (ad : addr) (m : mem) : tm -> Prop :=
  | acc_fun   : forall x Tx t, access ad m t  ->
                               access ad m <{fn x Tx t   }>

  | acc_call1 : forall t1 t2,  access ad m t1 ->
                               access ad m <{call t1 t2  }>

  | acc_call2 : forall t1 t2,  access ad m t2 ->
                               access ad m <{call t1 t2  }>

  | acc_memR  : forall ad' T,  ad <> ad'            ->
                               access ad m m[ad'].t ->
                               access ad m <{&ad' : `r&T`}>

  | acc_memW  : forall ad' T,  ad <> ad'            ->
                               access ad m m[ad'].t ->
                               access ad m <{&ad' : `w&T`}>

  | acc_refR  : forall T,      access ad m <{&ad : `r&T` }>

  | acc_refW  : forall T,      access ad m <{&ad : `w&T` }>

  | acc_new   : forall T t,    access ad m t  ->
                               access ad m <{new t : T   }>

  | acc_load  : forall t,      access ad m t  ->
                               access ad m <{*t          }>

  | acc_asg1  : forall t1 t2,  access ad m t1 ->
                               access ad m <{t1 := t2    }>

  | acc_asg2  : forall t1 t2,  access ad m t2 ->
                               access ad m <{t1 := t2    }>

  | acc_acq1  : forall t1 t2,  access ad m t1 ->
                               access ad m <{acq t1 t2   }>

  | acc_acq2  : forall t1 t2,  access ad m t2 ->
                               access ad m <{acq t1 t2   }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _acc tt :=
  match goal with
  | H : access _ _ <{unit     }>   |- _ => inv H
  | H : access _ _ <{nat _    }>   |- _ => inv H
  | H : access _ _ <{var _    }>   |- _ => inv H
  | H : access _ _ <{fn _ _ _ }>   |- _ => tt H
  | H : access _ _ <{call _ _ }>   |- _ => tt H
  | H : access _ _ <{& _ : _  }>   |- _ => tt H
  | H : access _ _ <{new _ : _}>   |- _ => tt H
  | H : access _ _ <{* _      }>   |- _ => tt H
  | H : access _ _ <{_ := _   }>   |- _ => tt H
  | H : access _ _ <{acq _  _ }>   |- _ => tt H
  | H : access _ _ <{cr _ _   }>   |- _ => inv H
  | H : access _ _ <{spawn _  }>   |- _ => inv H
  end.

Ltac inv_acc  := _acc inv.
Ltac invc_acc := _acc invc.

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
(* exclusive-access                                                          *)
(* ------------------------------------------------------------------------- *)

(* Access exclusively through a critical region. *)
Inductive exclusive_access (adx ad : addr) (m : mem) : tm -> Prop :=
  | xacc_fun    : forall x Tx t, exclusive_access adx ad m t  ->
                                 exclusive_access adx ad m <{fn x Tx t }>

  | xacc_call1  : forall t1 t2,  exclusive_access adx ad m t1 ->
                                 exclusive_access adx ad m <{call t1 t2}>

  | xacc_call2  : forall t1 t2,  exclusive_access adx ad m t2 ->
                                 exclusive_access adx ad m <{call t1 t2}>

  | xacc_new    : forall T t,    exclusive_access adx ad m t  ->
                                 exclusive_access adx ad m <{new t : T }>

  | xacc_load   : forall t,      exclusive_access adx ad m t  ->
                                 exclusive_access adx ad m <{*t        }>

  | xacc_asg1   : forall t1 t2,  exclusive_access adx ad m t1 ->
                                 exclusive_access adx ad m <{t1 := t2  }>

  | xacc_asg2   : forall t1 t2,  exclusive_access adx ad m t2 ->
                                 exclusive_access adx ad m <{t1 := t2  }>

  | xacc_acq1   : forall t1 t2,  exclusive_access adx ad m t1 ->
                                 exclusive_access adx ad m <{acq t1 t2 }>

  | xacc_acq2   : forall t1 t2,  exclusive_access adx ad m t2 ->
                                 exclusive_access adx ad m <{acq t1 t2 }>

  | xacc_cr_eq  : forall t,      access ad m t                ->
                                 exclusive_access adx ad m <{cr adx t  }>

  | xacc_cr_neq : forall adx' t, adx <> adx'                  ->
                                 exclusive_access adx ad m t  ->
                                 exclusive_access adx ad m <{cr adx' t }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _xacc tt :=
  match goal with
  | H : exclusive_access _ _ _ <{unit     }>   |- _ => inv H
  | H : exclusive_access _ _ _ <{nat _    }>   |- _ => inv H
  | H : exclusive_access _ _ _ <{var _    }>   |- _ => inv H
  | H : exclusive_access _ _ _ <{fn _ _ _ }>   |- _ => tt H
  | H : exclusive_access _ _ _ <{call _ _ }>   |- _ => tt H
  | H : exclusive_access _ _ _ <{& _ : _  }>   |- _ => inv H
  | H : exclusive_access _ _ _ <{new _ : _}>   |- _ => tt H
  | H : exclusive_access _ _ _ <{* _      }>   |- _ => tt H
  | H : exclusive_access _ _ _ <{_ := _   }>   |- _ => tt H
  | H : exclusive_access _ _ _ <{acq _  _ }>   |- _ => tt H
  | H : exclusive_access _ _ _ <{cr _ _   }>   |- _ => tt H
  | H : exclusive_access _ _ _ <{spawn _  }>   |- _ => inv H
  end.

Ltac inv_xacc  := _xacc inv.
Ltac invc_xacc := _xacc invc.

(* ------------------------------------------------------------------------- *)
(* not-access                                                                *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_cons_nacc := 
  intros ** ?; invc_acc; eauto.

Lemma nacc_unit : forall ad m,
  ~ access ad m <{unit}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_nat : forall ad m n,
  ~ access ad m <{nat n}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_var : forall ad m x,
  ~ access ad m <{var x}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_fun : forall ad m x Tx t,
  ~ access ad m t -> ~ access ad m <{fn x Tx t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_call : forall ad m t1 t2,
  ~ access ad m t1 -> ~ access ad m t2 -> ~ access ad m <{call t1 t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_ref : forall ad m ad' T,
  ad <> ad' -> ~ access ad m m[ad'].t -> ~ access ad m <{&ad' : T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_new : forall ad m t T,
  ~ access ad m t -> ~ access ad m <{new t : T}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_load : forall ad m t,
  ~ access ad m t -> ~ access ad m <{*t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_asg : forall ad m t1 t2,
  ~ access ad m t1 -> ~ access ad m t2 -> ~ access ad m <{t1 := t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_acq : forall ad m t1 t2,
  ~ access ad m t1 -> ~ access ad m t2 -> ~ access ad m <{acq t1 t2}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_cr : forall ad m adx t,
  ~ access ad m <{cr adx t}>.
Proof. solve_cons_nacc. Qed.

Lemma nacc_spawn : forall ad m t,
  ~ access ad m <{spawn t}>.
Proof. solve_cons_nacc. Qed.

#[export] Hint Resolve
  nacc_unit  nacc_nat
  nacc_var   nacc_fun nacc_call
  nacc_ref   nacc_new nacc_load nacc_asg
  nacc_acq   nacc_cr
  nacc_spawn
  : not_access.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_nacc := 
  intros; try split; eauto using access.

Local Lemma inv_nacc_fun : forall m x Tx t ad,
  ~ access ad m <{fn x Tx t}> -> ~ access ad m t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_call : forall m t1 t2 ad,
  ~ access ad m <{call t1 t2}> -> ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_refR : forall m ad ad' T,
  ~ access ad m <{&ad' : `r&T`}> ->
  ad <> ad' /\ ~ access ad m m[ad'].t.
Proof.
  intros. assert (ad <> ad') by (intros ?; subst; eauto using access).
  split; eauto using access.
Qed.

Local Lemma inv_nacc_refW : forall m ad ad' T,
  ~ access ad m <{&ad' : `w&T`}> ->
  ad <> ad' /\ ~ access ad m m[ad'].t.
Proof.
  intros. assert (ad <> ad') by (intros ?; subst; eauto using access).
  split; eauto using access.
Qed.

Local Lemma inv_nacc_new : forall m t ad T,
  ~ access ad m <{new t : T}> -> ~ access ad m t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_load : forall m t ad,
  ~ access ad m <{*t}> -> ~ access ad m t.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_asg : forall m t1 t2 ad,
  ~ access ad m <{t1 := t2}> -> ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_inv_nacc. Qed.

Local Lemma inv_nacc_acq : forall m t1 t2 ad,
  ~ access ad m <{acq t1 t2}> -> ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_inv_nacc. Qed.

Ltac invc_nacc :=
  match goal with
  | H : ~ access _ _ <{unit       }> |- _ => clear H
  | H : ~ access _ _ <{nat _      }> |- _ => clear H
  | H : ~ access _ _ <{var _      }> |- _ => clear H
  | H : ~ access _ _ <{fn _ _ _   }> |- _ => eapply inv_nacc_fun  in H
  | H : ~ access _ _ <{call _ _   }> |- _ => eapply inv_nacc_call in H as [? ?]
  | H : ~ access _ _ <{& _ : `r&_`}> |- _ => eapply inv_nacc_refR in H as [? ?]
  | H : ~ access _ _ <{& _ : `x&_`}> |- _ => clear H
  | H : ~ access _ _ <{& _ : `w&_`}> |- _ => eapply inv_nacc_refW in H as [? ?]
  | H : ~ access _ _ <{new _ : _  }> |- _ => eapply inv_nacc_new  in H
  | H : ~ access _ _ <{* _        }> |- _ => eapply inv_nacc_load in H
  | H : ~ access _ _ <{_ := _     }> |- _ => eapply inv_nacc_asg  in H as [? ?]
  | H : ~ access _ _ <{acq _ _    }> |- _ => eapply inv_nacc_acq  in H as [? ?]
  | H : ~ access _ _ <{cr _ _     }> |- _ => clear H
  | H : ~ access _ _ <{spawn _    }> |- _ => clear H
  end.

(* lemmas ------------------------------------------------------------------ *)

Lemma nacc_mem : forall m t,
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  ~ access (#m) m t.
Proof.
  intros ** Hacc. induction Hacc; invc_vr; eauto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma nacc_subst : forall ad m x tx t,
  ~ access ad m t ->
  ~ access ad m tx ->
  ~ access ad m <{[x := tx] t}>.
Proof.
  intros * Ht Htx. induction t; trivial; simpl in *; invc_nacc;
  try destruct str_eq_dec; eauto with not_access.
Qed.

Local Lemma nacc_mem_set1 : forall m t ad ad' t' T',
  ~ access ad m t' ->
  ~ access ad m t  ->
  ~ access ad m[ad'.tT <- t' T'] t.
Proof.
  intros ** Hacc. induction Hacc; eauto using access;
  repeat omicron; invc_nacc; eauto with not_access.
Qed.

Local Lemma nacc_mem_set2 : forall m t ad ad' c,
  ~ access ad' m t ->
  ~ access ad  m t ->
  ~ access ad  m[ad' <- c] t.
Proof.
  intros ** Hacc.
  induction Hacc; repeat invc_nacc; eauto using access; sigma; eauto.
Qed.

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

(* ------------------------------------------------------------------------- *)
(* pointer types                                                             *)
(* ------------------------------------------------------------------------- *)

Theorem ptyp_preservation : forall m1 m2 ths1 ths2 tid e ad,
  valid_references m1 ths1[tid] ->
  (* --- *)
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  ad < #m1 ->
  m1[ad].T = m2[ad].T.
Proof.
  intros. invc_cstep; trivial. invc_mstep; sigma; trivial;
  omicron; trivial. ind_tstep; repeat invc_vr; eauto.
Qed.

Lemma ptyp_wacc_correlation : forall m t ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad m t ->
  write_access ad m t <-> (exists T, m[ad].T = `w&T`).
Proof.
  intros * ? Hmvr ? Hacc. split.
  - intros Hwacc. clear Hacc. induction Hwacc; invc_vr; eauto.
  - intros [? ?]. induction Hacc; invc_vr; eauto using write_access.
    exfalso. eapply safe_then_nwacc; eauto.
Qed.

Corollary wacc_by_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t ->
  valid_references m t' ->
  (* --- *)
  access ad m t ->
  write_access ad m t' ->
  write_access ad m t.
Proof.
  intros.
  eapply ptyp_wacc_correlation; eauto.
  eapply ptyp_wacc_correlation; eauto using wacc_then_acc.
Qed.

Lemma ptyp_racc_correlation : forall m t ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad m t ->
  read_access ad m t <-> (exists T, m[ad].T = `r&T`).
Proof.
  intros * Hval ? ? Hacc. split; intros [? ?].
  - induction Hacc; invc_vr; invc_nwacc; eauto using safe_then_nwacc.
  - split; trivial. induction Hacc; intros ?; invc_vr; inv_wacc; eauto;
    eapply IHHacc; eauto using wacc_by_association.
Qed.

Corollary racc_by_association : forall m t t' ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t ->
  valid_references m t' ->
  (* --- *)
  access ad m t ->
  read_access ad m t' ->
  read_access ad m t.
Proof.
  intros * ? ? ? ? ? Hracc.
  eapply ptyp_racc_correlation; eauto.
  duplicate Hracc Hracc'. destruct Hracc' as [? ?].
  eapply ptyp_racc_correlation; eauto.
Qed.

Theorem ptyp_racc_wacc_contradiction : forall m1 m2 t1 t2 ad,
  forall_memory m1 value ->
  forall_memory m2 value ->
  forall_memory m1 (valid_references m1) ->
  forall_memory m2 (valid_references m2) ->
  valid_references m1 t1 ->
  valid_references m2 t2 ->
  (* --- *)
  m1[ad].T = m2[ad].T ->
  read_access  ad m1 t1 ->
  write_access ad m2 t2 ->
  False.
Proof.
  intros until 7. intros Hracc Hwacc.
  eapply ptyp_racc_correlation in Hracc as [? Htyp1];
  eauto using racc_then_acc.
  eapply ptyp_wacc_correlation in Hwacc as [? Htyp2];
  eauto using wacc_then_acc.
  rewrite Htyp1 in *. rewrite Htyp2 in *. discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* access-promise-1                                                          *)
(* ------------------------------------------------------------------------- *)

Definition access_promise1 (ad : addr) (m : mem) (t : tm) :=  forall adx T,
  m[ad].T = `w&T` ->
  exclusive_access adx ad m t ->
  access ad m t ->
  False.

(* constructors ------------------------------------------------------------ *)

Local Lemma ap1_unit : forall ad m,
  access_promise1 ad m <{unit}>.
Proof.
  intros until 3. invc_xacc.
Qed.

Local Lemma ap1_nat : forall ad m n,
  access_promise1 ad m <{nat n}>.
Proof.
  intros until 3. invc_xacc.
Qed.

Local Lemma ap1_ref : forall ad m n,
  access_promise1 ad m <{nat n}>.
Proof.
  intros until 3. invc_xacc.
Qed.

Local Lemma ap1_var : forall ad m x,
  access_promise1 ad m <{var x}>.
Proof.
  intros until 3. invc_xacc.
Qed.

Local Lemma ap1_fun : forall ad m x Tx t,
  access_promise1 ad m t -> access_promise1 ad m <{fn x Tx t}>.
Proof.
  intros until 4. invc_acc; invc_xacc. eauto.
Qed.

Local Lemma ap1_call : forall ad m t1 t2,
  access_promise1 ad m t1 ->
  access_promise1 ad m t2 ->
  access_promise1 ad m <{call t1 t2}>.
Proof.
  intros. intros until 3. invc_acc; invc_xacc; eauto.
Abort.

#[export] Hint Resolve
  ap1_unit  ap1_nat
  ap1_var   ap1_fun
  ap1_ref
  : ap1.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_ap1 :=
  intros; try split; intros until 3; eauto using access, exclusive_access. 

Local Lemma inv_ap1_fun : forall ad m x Tx t,
  access_promise1 ad m <{fn x Tx t}> ->
  access_promise1 ad m t.
Proof. solve_inv_ap1. Qed.

Local Lemma inv_ap1_call : forall ad m t1 t2,
  access_promise1 ad m <{call t1 t2}> ->
  access_promise1 ad m t1 /\ access_promise1 ad m t2.
Proof. solve_inv_ap1. Qed.

Ltac dup_apply1 H L := specialize H as H'; eapply L in H.
Ltac dup_apply2 H L := specialize H as H'; eapply L in H as [? ?].

Ltac inv_ap1 :=
  match goal with
  | H : access_promise1 _ _ <{fn _ _ _   }> |- _ => dup_apply1 H inv_ap1_fun
  | H : access_promise1 _ _ <{call _ _   }> |- _ => dup_apply2 H inv_ap1_call
  end.

(* preservation ------------------------------------------------------------ *)

Local Lemma acc_subst_backwards : forall ad m x tx t,
  access ad m <{[x := tx] t}> ->
  access ad m tx \/ access ad m t.
Proof.
  intros. induction t; eauto; simpl in *; try destruct str_eq_dec; eauto;
  invc_acc; aspecialize;
  match goal with H : _ \/ _ |- _ => destruct H end;
  eauto using access.
Qed.

Local Lemma xacc_subst_backwads : forall adx ad m x tx t,
  exclusive_access adx ad m <{ [x := tx] t }> ->
  (exclusive_access adx ad m tx \/
   exclusive_access adx ad m t  \/
   access ad m <{[x := tx] t}>  ).
Proof.
  intros. induction t; eauto; simpl in *; try destruct str_eq_dec; eauto;
  inv_xacc; try aspecialize;
  try solve [
    match goal with H : _ \/ _ \/ _ |- _ => decompose sum H end;
    eauto using access, exclusive_access
  ].
  - eapply acc_subst_backwards in H1 as [? | ?];
    eauto using exclusive_access.
    exfalso.
    admit.
  - destruct IHt as [? | [? | ?]]; eauto.
    + right. left. eapply xacc_cr_neq; eauto.
    + exfalso. (*H0 e H3*)
Abort.

Local Lemma ap1_subst : forall ad m x tx Tx t,
  access_promise1 ad m <{call (fn x Tx t) tx}> ->
  access_promise1 ad m t ->
  access_promise1 ad m tx ->
  access_promise1 ad m <{[x := tx] t}>.
Proof.
  intros * H Ht Htx. intros until 3.
  specialize (Ht adx T H0).
  specialize (Htx adx T H0).
  assert (Hacc : access ad m tx \/ access ad m t)
    by eauto using acc_subst_backwards.
  destruct Hacc; repeat aspecialize;
  eauto using access, exclusive_access.
  - admit.
  - admit.
Abort.

Local Lemma ap1_preservation_none : forall ad m t1 t2,
  access_promise1 ad m t1 ->
  t1 --[e_none]--> t2 ->
  access_promise1 ad m t2.
Proof.
  intros * Hap ?. ind_tstep; repeat clean.
  - inv_ap1. repeat aspecialize. intros until 3.
    invc_xacc; invc_acc; eauto.
    + assert (exclusive_access adx ad m t1) by admit.
      eauto using access, exclusive_access.
    + assert (access ad m t1) by admit.
      eauto using access, exclusive_access.
  - admit.
  - inv_ap1. eapply inv_ap1_fun in H0 as ?.




    intros until 3; eauto using access, exclusive_access.
  - intros until 2.
Qed.

Local Lemma ap1_preservation_mstep : forall m1 m2 ths tid t e,
  xacc_acc_promise m1 ths ->
  m1 / ths[tid] ==[e]==> m2 / t ->
  xacc_acc_promise m2 ths[tid <- t].
Proof.
  intros. invc_mstep.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.
















(* ------------------------------------------------------------------------- *)
(* guards                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition guards adx ad m :=
  exists T, m[adx].T = `x&T` /\ access ad m m[adx].t.

(* ------------------------------------------------------------------------- *)
(* guard-promise                                                             *)
(* ------------------------------------------------------------------------- *)

Definition guard_promise (m : mem) (t : tm) := forall adx ad T,
  m[ad].T = `w&T` ->
  guards adx ad m ->
  ~ access ad m t.

Local Ltac solve_cons_gp :=
  intros ** ? ? ? ? ?; eauto with not_access.

Lemma gp_unit : forall m,
  guard_promise m <{unit}>.
Proof. solve_cons_gp. Qed.

Lemma gp_nat : forall m n,
  guard_promise m <{nat n}>.
Proof. solve_cons_gp. Qed.

Lemma gp_var : forall m x,
  guard_promise m <{var x}>.
Proof. solve_cons_gp. Qed.

Lemma gp_fun : forall m x Tx t,
  guard_promise m t -> guard_promise m <{fn x Tx t}>.
Proof. solve_cons_gp. Qed.

Lemma gp_call : forall m t1 t2,
  guard_promise m t1 -> guard_promise m t2 -> guard_promise m <{call t1 t2}>.
Proof. solve_cons_gp. Qed.

(* gp_ref *)

Lemma gp_new : forall m t T,
  guard_promise m t -> guard_promise m <{new t : T}>.
Proof. solve_cons_gp. Qed.

Lemma gp_load : forall m t,
  guard_promise m t -> guard_promise m <{*t}>.
Proof. solve_cons_gp. Qed.

Lemma gp_asg : forall m t1 t2,
  guard_promise m t1 -> guard_promise m t2 -> guard_promise m <{t1 := t2}>.
Proof. solve_cons_gp. Qed.

Lemma gp_acq : forall m t1 t2,
  guard_promise m t1 -> guard_promise m t2 -> guard_promise m <{acq t1 t2}>.
Proof. solve_cons_gp. Qed.

Lemma gp_cr : forall m adx t,
  guard_promise m <{cr adx t}>.
Proof. solve_cons_gp. Qed.

Lemma gp_spawn : forall m t,
  guard_promise m <{spawn t}>.
Proof. solve_cons_gp. Qed.

#[export] Hint Resolve
  gp_unit gp_nat
  gp_var  gp_fun gp_call
  gp_new  gp_load gp_asg
  gp_acq  gp_cr
  gp_spawn
  : guard_promise.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_gp :=
  intros * H; try split; intros ? ? ? Had Hguards ?;
  eapply H; eauto using access.

Local Lemma inv_gp_fun : forall m x Tx t,
  guard_promise m <{fn x Tx t}> -> guard_promise m t.
Proof. solve_inv_gp. Qed. 

Local Lemma inv_gp_call : forall m t1 t2,
  guard_promise m <{call t1 t2}> -> guard_promise m t1 /\ guard_promise m t2.
Proof. solve_inv_gp. Qed. 

Local Lemma inv_gp_new : forall m t T,
  guard_promise m <{new t : T}> -> guard_promise m t.
Proof. solve_inv_gp. Qed.

Local Lemma inv_gp_load : forall m t,
  guard_promise m <{*t}> -> guard_promise m t.
Proof. solve_inv_gp. Qed.

Local Lemma inv_gp_asg : forall m t1 t2,
  guard_promise m <{t1 := t2}> -> guard_promise m t1 /\ guard_promise m t2.
Proof. solve_inv_gp. Qed.

Local Lemma inv_gp_acq : forall m t1 t2,
  guard_promise m <{acq t1 t2}> -> guard_promise m t1 /\ guard_promise m t2.
Proof. solve_inv_gp. Qed.

Ltac invc_gp :=
  match goal with
  | H : guard_promise _ <{unit     }> |- _ => clear H
  | H : guard_promise _ <{nat _    }> |- _ => clear H
  | H : guard_promise _ <{var _    }> |- _ => clear H
  | H : guard_promise _ <{fn _ _ _ }> |- _ => eapply inv_gp_fun    in H
  | H : guard_promise _ <{call _ _ }> |- _ => eapply inv_gp_call   in H as [? ?]
  | H : guard_promise _ <{& _ : _  }> |- _ => idtac H (* TODO *)
  | H : guard_promise _ <{new _ : _}> |- _ => eapply inv_gp_new    in H
  | H : guard_promise _ <{* _      }> |- _ => eapply inv_gp_load   in H
  | H : guard_promise _ <{_ := _   }> |- _ => eapply inv_gp_asg    in H as [? ?]
  | H : guard_promise _ <{acq _ _  }> |- _ => eapply inv_gp_acq    in H as [? ?]
  | H : guard_promise _ <{cr _ _   }> |- _ => clear H
  | H : guard_promise _ <{spawn _  }> |- _ => clear H
  end.

(* lemmas ------------------------------------------------------------------ *)

Lemma gp_tstep_write_term : forall m t1 t2 ad t T,
  guard_promise m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  guard_promise m t.
Proof.
  intros. ind_tstep; try solve [invc_gp; eauto with guard_promise].
  repeat clean.
Abort.

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma acc_mem_set_X_backwards : forall m t ad ad' X,
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad m[ad'.X <- X] t ->
  access ad m t.
Proof.
  intros * ? ? Hacc. induction Hacc; invc_vr; eauto using access;
  omicron; eauto using access.
Qed.

Local Lemma acc_mem_set_tT_backwards1 : forall m t ad ad' t' T',
  ~ access ad m t' ->
  (* --- *)
  access ad m[ad'.tT <- t' T'] t ->
  access ad m t.
Proof.
  intros * ? Hacc. remember (m[ad'.tT <- t' T']) as m'.
  induction Hacc; inv Heqm'; eauto using access;
  match goal with |- access _ _ <{& ?ad : _}> => rename ad into ad'' end;
  destruct (nat_eq_dec ad' ad''); subst; try (sigma; eauto using access);
  destruct (nat_eq_dec ad'' ad); subst; eauto using access;
  rewrite (set_get_eq cell_default) in IHHacc; try contradiction;
  omicron; eauto; inv_acc.
Qed.

Lemma acc_mem_set_tT_backwards2 : forall m t ad ad' c,
  ~ access ad' m t ->
  (* --- *)
  access ad m[ad' <- c] t ->
  access ad m t.
Proof.
  intros * ? Hacc. induction Hacc; invc_nacc; eauto using access;
  sigma; eauto using access.
Qed.

Local Lemma gp_mem_set_X : forall m t ad X,
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  guard_promise m t ->
  guard_promise m[ad.X <- X] t.
Proof.
  intros * ? ? Hgp. induction t;
  try solve [try inv_vr; invc_gp; eauto with guard_promise].
  intros ? ? ? ? [? [? ?]] ?.
  repeat omicron; eauto; try discriminate;
  eapply Hgp; eauto; try eexists; eauto using acc_mem_set_X_backwards.
Qed.

Local Lemma gp_mem_set_tT : forall m t ad t' T',
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  m[ad].T = `w&T'` ->
  guard_promise m t ->
  guard_promise m[ad.tT <- t' `w&T'`] t.
Proof.
  intros * ? ? ? Hgp. induction t;
  try solve [try inv_vr; invc_gp; eauto with guard_promise].
  intros ? ? ? ? [? [? ?]] ?.
  repeat omicron; eauto; try discriminate.
  - invc H2.
    eapply Hgp; eauto.
    + eexists. admit.
    + eapply acc_mem_set_tT_backwards1; eauto.
      admit.
  - admit.
Abort.

(* preservation ------------------------------------------------------------ *)

Local Lemma gp_preservation_none : forall m t1 t2,
  guard_promise m t1 ->
  t1 --[e_none]--> t2 ->
  guard_promise m t2.
Proof.
  intros. ind_tstep; intros until 2; repeat invc_gp;
  unfold guard_promise in *; eauto using nacc_subst with not_access.
Qed.






Lemma nacc_mem_add : forall m t ad tT,
  ~ access (#m) m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad (m +++ tT) t.
Proof.
  intros ** Hacc. induction Hacc; repeat invc_nacc; eauto; omicron; eauto.
Qed.

Local Lemma acc_mem_add : forall ad m t t' T',
  ad < #m ->
  access ad m t ->
  access ad (m +++ (t', T', false)) t.
Proof.
  intros * ? Hacc. induction Hacc; eauto using access;
  (eapply acc_memR || eapply acc_memW); eauto; omicron; eauto; invc_acc.
Qed.

Lemma acc_mem_add_backwards : forall m t ad c,
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad (m +++ c) t ->
  access ad m t.
Proof.
  intros * ? Hvr Hacc.
  assert (Hnacc : ~ access (#m) m t) by eauto using nacc_vr_length.
  clear Hvr. induction Hacc; invc_nacc; eauto using access;
  omicron; eauto using access; invc_acc.
Qed.

Local Lemma guards_mem_add : forall adx ad m t T,
  ad < #m ->
  guards adx ad m ->
  guards adx ad (m +++ (t, T, false)).
Proof.
  intros * ? [Tx [Hadx Hacc]]. exists Tx. split;
  omicron; eauto using acc_mem_add; discriminate.
Qed.

Local Lemma guards_mem_add_backwards : forall adx ad m t T,
  forall_memory m (valid_references m) ->
  (* --- *)
  adx < #m ->
  guards adx ad (m +++ (t, T, false)) ->
  guards adx ad m.
Proof.
  intros * ? ? [Tx [Hadx Hacc]]. sigma. eexists.
  eauto using acc_mem_add_backwards.
Qed.

Local Lemma gp_preservation_alloc : forall m t1 t2 t T,
  forall_memory m (valid_references m) ->
  valid_references m t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  guard_promise (m +++ (t, T, false)) t2.
Proof.
  intros. ind_tstep; invc_vr; invc_gp;
  repeat clean.
  - repeat aspecialize.
    intros adx ad Tw Had Hguards.
    eapply nacc_call; eauto.
    destruct Hguards as [Tx [Hadx Hacc]]. omicron; subst.
    + omicron; subst; try discriminate.
      * eapply acc_mem_add_backwards in Hacc; eauto.
        specialize (H1 adx ad Tw Had).
        eapply nacc_mem_add; eauto using nacc_vr_length.
        eapply H1.
        eexists; eauto.
      * eapply acc_mem_add_backwards in Hacc; eauto.
        contradict Hacc.
        eapply nacc_vr_length; eauto.
    + omicron; try discriminate.
      eapply acc_mem_add_backwards in Hacc; eauto using vr_tstep_alloc_term.
      eapply nacc_mem_add; eauto using nacc_vr_length.
      admit.
    + invc_acc.
Abort.


x& (Nat)

x& (&w (w& Nat))

m.acq (&t
---


m.set (t)


new t : x&T --[e]--> new t' : x&T

new t : ... --[e_none]--> newx ad t

new v : x&T --[e]--> &ad : x&T






Local Lemma gp_preservation_read : forall m t1 t2 ad,
  well_typed_term t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_read ad m[ad].t]--> t2 ->
  guard_promise m t2.
Proof.
  intros * [T Htypeof] **. generalize dependent T.
  ind_tstep; intros until 3; invc_gp; 
  try solve [invc_typeof; unfold guard_promise in *; eauto with not_access].
  match goal with
  |  Hgp : guard_promise m _
  ,  Hty : m[?ad].T = `w&?T`
  ,  Hg  : guards adx ?ad m
  |- _ =>
      specialize (Hgp adx ad T Hty Hg)
  end.
  repeat invc_typeof; invc_nacc; trivial. 
Qed.

Local Lemma wtt_tstep_write_type : forall t1 t2 ad t T,
  well_typed_term t1 ->
  t1 --[e_write ad t T]--> t2 ->
  exists Tw, T = `w&Tw`.
Proof.
  intros * [T ?] **. gendep T. ind_tstep; intros; repeat invc_typeof; eauto.
Qed.

Local Lemma gp_preservation_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  guard_promise m[ad.tT <- t T] t2.
Proof.
  intros. ind_tstep; invc_wtt; invc_gp.
  - eapply gp_call; eauto.
    duplicate H1 Htstep.
    eapply wtt_tstep_write_type in H1 as [? ?]; eauto; subst.
    clean.
Abort.

Local Lemma gp_preservation_acq : forall m t1 t2 ad t,
  forall_memory m (valid_references m) ->
  valid_references m t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  guard_promise m[ad.X <- true] t2.
Proof.
  intros. ind_tstep; invc_vr; invc_gp;
  eauto using gp_mem_set_X with guard_promise.
Qed.

Local Lemma gp_preservation_rel : forall m t1 t2 ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t1 ->
  safe_boundaries t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_rel ad]--> t2 ->
  guard_promise m[ad.X <- false] t2.
Proof.
  intros. ind_tstep; invc_vr; invc_sb; invc_gp;
  eauto using gp_mem_set_X with guard_promise.
  eapply gp_mem_set_X; eauto. intros until 2.
  invc_sval; eauto with not_access; invc_vr; intros ?; invc_acc; eauto.
  eapply nwacc_from_safe_type; eauto.
  eapply ptyp_wacc_correlation; eauto.
Qed.

Local Lemma gp_preservation_spawn : forall m t1 t2 tid t,
  guard_promise m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  guard_promise m t2.
Proof.
  intros. ind_tstep; intros until 2; repeat invc_gp;
  unfold guard_promise in *; eauto with not_access.
Qed.

Local Lemma gp_preservation_mstep : forall m1 m2 t1 t2 e,
  forall_memory m1 value ->
  well_typed_term t1 ->
  forall_memory m1 (valid_references m1) ->
  valid_references m1 t1 ->
  safe_boundaries t1 ->
  (* --- *)
  guard_promise m1 t1 ->
  m1 / t1 ==[e]==> m2 / t2 ->
  guard_promise m2 t2.
Proof.
  intros. invc_mstep;
  eauto using gp_preservation_none;
  (* eauto using gp_preservation_alloc; *)
  eauto using gp_preservation_read;
  (* eauto using gp_preservation_write; *)
  eauto using gp_preservation_acq;
  eauto using gp_preservation_rel;
  eauto using gp_preservation_spawn.
  - admit.
  - admit.
Qed.

Theorem gp_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (valid_references m1) ->
  (* --- *)
  forall_threads ths1 (guard_promise m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (guard_promise m2).
Proof.
  intros. invc_cstep.
Qed.


