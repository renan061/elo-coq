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

(* ------------------------------------------------------------------------- *)
(* read-access                                                              *)
(* ------------------------------------------------------------------------- *)

Definition read_access (ad : addr) (m : mem) (t : tm) :=
  access ad m t /\ ~ write_access ad m t.

(* ------------------------------------------------------------------------- *)
(* guards                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition guards adx ad m :=
  exists T, m[adx].T = `x&T` /\ access ad m m[adx].t.

(* lemmas ------------------------------------------------------------------ *)

Lemma guards_adx_lt : forall adx ad m,
  guards adx ad m ->
  adx < #m.
Proof.
  intros * [? [? ?]].
  decompose sum (lt_eq_lt_dec adx (#m)); subst; trivial; sigma; discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* guarded-access                                                            *)
(* ------------------------------------------------------------------------- *)

(* Access (exclusively) through a critical region. *)
Inductive guarded_access (adx ad : addr) (m : mem) : tm -> Prop :=
  | xacc_fun    : forall x Tx t, guarded_access adx ad m t  ->
                                 guarded_access adx ad m <{fn x Tx t }>

  | xacc_call1  : forall t1 t2,  guarded_access adx ad m t1 ->
                                 guarded_access adx ad m <{call t1 t2}>

  | xacc_call2  : forall t1 t2,  guarded_access adx ad m t2 ->
                                 guarded_access adx ad m <{call t1 t2}>

  | xacc_new    : forall T t,    guarded_access adx ad m t  ->
                                 guarded_access adx ad m <{new t : T }>

  | xacc_load   : forall t,      guarded_access adx ad m t  ->
                                 guarded_access adx ad m <{*t        }>

  | xacc_asg1   : forall t1 t2,  guarded_access adx ad m t1 ->
                                 guarded_access adx ad m <{t1 := t2  }>

  | xacc_asg2   : forall t1 t2,  guarded_access adx ad m t2 ->
                                 guarded_access adx ad m <{t1 := t2  }>

  | xacc_acq1   : forall t1 t2,  guarded_access adx ad m t1 ->
                                 guarded_access adx ad m <{acq t1 t2 }>

  | xacc_acq2   : forall t1 t2,  guarded_access adx ad m t2 ->
                                 guarded_access adx ad m <{acq t1 t2 }>

  | xacc_cr_eq  : forall t,      access ad m t              ->
                                 guarded_access adx ad m <{cr adx t  }>

  | xacc_cr_neq : forall adx' t, adx <> adx'                ->
                                 guarded_access adx ad m t  ->
                                 guarded_access adx ad m <{cr adx' t }>
  .

(* ------------------------------------------------------------------------- *)
(* inversions                                                                *)
(* ------------------------------------------------------------------------- *)

Local Ltac _acc_racc_wacc P tt :=
  match goal with
  | H : P _ _ <{unit     }>   |- _ => inv H
  | H : P _ _ <{nat _    }>   |- _ => inv H
  | H : P _ _ <{var _    }>   |- _ => inv H
  | H : P _ _ <{fn _ _ _ }>   |- _ => tt H
  | H : P _ _ <{call _ _ }>   |- _ => tt H
  | H : P _ _ <{& _ : _  }>   |- _ => tt H
  | H : P _ _ <{new _ : _}>   |- _ => tt H
  | H : P _ _ <{* _      }>   |- _ => tt H
  | H : P _ _ <{_ := _   }>   |- _ => tt H
  | H : P _ _ <{acq _  _ }>   |- _ => tt H
  | H : P _ _ <{cr _ _   }>   |- _ => inv H
  | H : P _ _ <{spawn _  }>   |- _ => inv H
  end.

Ltac inv_acc  := _acc_racc_wacc access inv.
Ltac invc_acc := _acc_racc_wacc access invc.

Ltac inv_wacc  := _acc_racc_wacc write_access inv.
Ltac invc_wacc := _acc_racc_wacc write_access invc.

Ltac inv_racc  := _acc_racc_wacc read_access inv.
Ltac invc_racc := _acc_racc_wacc read_access invc.

Local Ltac _xacc tt :=
  match goal with
  | H : guarded_access _ _ _ <{unit     }>   |- _ => inv H
  | H : guarded_access _ _ _ <{nat _    }>   |- _ => inv H
  | H : guarded_access _ _ _ <{var _    }>   |- _ => inv H
  | H : guarded_access _ _ _ <{fn _ _ _ }>   |- _ => tt H
  | H : guarded_access _ _ _ <{call _ _ }>   |- _ => tt H
  | H : guarded_access _ _ _ <{& _ : _  }>   |- _ => inv H
  | H : guarded_access _ _ _ <{new _ : _}>   |- _ => tt H
  | H : guarded_access _ _ _ <{* _      }>   |- _ => tt H
  | H : guarded_access _ _ _ <{_ := _   }>   |- _ => tt H
  | H : guarded_access _ _ _ <{acq _  _ }>   |- _ => tt H
  | H : guarded_access _ _ _ <{cr _ _   }>   |- _ => tt H
  | H : guarded_access _ _ _ <{spawn _  }>   |- _ => inv H
  end.

Ltac inv_cacc  := _xacc inv.
Ltac invc_cacc := _xacc invc.

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
  nacc_unit nacc_nat
  nacc_var nacc_fun nacc_call
  nacc_ref nacc_new nacc_load nacc_asg
  nacc_acq nacc_cr
  nacc_spawn
  : not_access.

(* inversions -------------------------------------------------------------- *)

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
(* ptyp preservation                                                         *)
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

(* ------------------------------------------------------------------------- *)
(* ptyp & wacc/racc                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma wacc_then_acc : forall ad m t,
  write_access ad m t ->
  access ad m t.
Proof.
  intros * Hwacc. induction Hwacc; eauto using access.
Qed.

Corollary racc_then_acc : forall ad m t,
  read_access ad m t ->
  access ad m t.
Proof.
  intros * [? _]. assumption.
Qed.

Lemma nwacc_from_safe_type : forall m ad ad' T,
  forall_memory m value ->
  empty |-- m[ad'].t is `Safe T` ->
  ~ write_access ad m m[ad'].t.
Proof.
  intros * Hval **. intros ?.
  specialize (Hval ad'); simpl in *.
  destruct Hval; inv_typeof; inv_wacc; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma ptyp_wacc_correlation : forall m t ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad m t ->
  write_access ad m t <-> (exists T, m[ad].T = `w&T`).
Proof.
  intros * ? Hmvr ? Hacc. split.
  - intros Hwacc. clear Hacc. induction Hwacc; inv_vr; eauto.
  - intros [? Heq]. induction Hacc; inv_vr; eauto using write_access.
    exfalso. eapply nwacc_from_safe_type; eauto.
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
  - induction Hacc; invc_vr; invc_nwacc; eauto using nwacc_from_safe_type.
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
  specialize Hracc as Hracc'. destruct Hracc' as [? ?].
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
  eapply ptyp_racc_correlation in Hracc as [? Htyp1]; eauto using racc_then_acc.
  eapply ptyp_wacc_correlation in Hwacc as [? Htyp2]; eauto using wacc_then_acc.
  rewrite Htyp1 in *. rewrite Htyp2 in *. discriminate.
Qed.





















(* ------------------------------------------------------------------------- *)
(* valid_access_types                                                        *)
(* ------------------------------------------------------------------------- *)

Definition valid_access_types (m : mem) := forall ad1 ad2 T1 T2,
  access ad1 m m[ad2].t ->
  m[ad1].T = `w&T1` ->
  m[ad2].T = `r&T2` ->
  False.

(* preservation ------------------------------------------------------------ *)

Local Lemma acc_mem_setX : forall m t ad ad' X,
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad m t ->
  access ad m[ad'.X <- X] t.
Proof.
  intros * ? ? Hacc. induction Hacc; repeat invc_vr; eauto using access.
  - eapply acc_memR; trivial. omicron; eauto.
  - eapply acc_memW; trivial. omicron; eauto.
Qed.

Local Lemma acc_mem_setX' : forall m t ad ad' X,
  ad' < #m ->
  access ad m[ad'.X <- X] t ->
  access ad m t.
Proof.
  intros * ? Hacc.
  induction Hacc; repeat invc_vr; eauto using access.
  - eapply acc_memR; trivial. omicron; eauto.
  - eapply acc_memW; trivial. omicron; eauto.
Qed.

Local Lemma vat_preservation_mstep : forall m1 m2 t1 t2 e,
  valid_access_types m1 ->
  m1 / t1 ==[e]==> m2 / t2 ->
  valid_access_types m2.
Proof.
  intros. invc_mstep; trivial.
  - admit.
  - ind_tstep; eauto; repeat clean.
    intros ad1 ad2 T1 T2 Hacc Had1 Had2. repeat omicron; subst;
    try discriminate.
    + admit.
    + admit.
    + admit.
Abort.

(* ------------------------------------------------------------------------- *)
(* guard-promise                                                             *)
(* ------------------------------------------------------------------------- *)

Definition guard_promise (m : mem) (t : tm) := forall adx ad T,
  m[ad].T = `w&T` ->
  guards adx ad m ->
  ~ access ad m t.

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

(* preservation ------------------------------------------------------------ *)

Local Lemma nacc_subst : forall ad m x tx t,
  ~ access ad m t ->
  ~ access ad m tx ->
  ~ access ad m <{[x := tx] t}>.
Proof.
  intros * Ht Htx. induction t; trivial; simpl in *; invc_nacc;
  try destruct str_eq_dec; eauto with not_access.
Qed.

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

Local Lemma gp_mem_add : forall m t t' T',
  valid_references m t ->
  (* --- *)
  guard_promise m t ->
  guard_promise (m +++ (t', T', false)) t.
Proof.
  intros. induction t; repeat invc_vr; invc_gp; 
  try solve [repeat aspecialize;
             unfold guard_promise; intros; eauto with not_access].
  - rename a into ad'.
    intros adx ad T'' Had Hguards.
    specialize (H0 adx ad T'').
    omicron.
    + aspecialize.
    eapply nacc_mem_add; eauto.
    unfold guard_promise; intros; eauto with not_access.
Qed.

Local Lemma gp_preservation_alloc : forall m t1 t2 t T,
  guard_promise m t1 ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  guard_promise (m +++ (t, T, false)) t2.
Proof.
  intros. ind_tstep; invc_gp;
  repeat clean.
  - repeat aspecialize. 
    intros adx ad Tx Had Hguards Hacc. omicron.
    +
  



  - unfold guard_promise in *; eauto with not_access.


  intros. ind_tstep; intros until 2; repeat invc_gp;
  unfold guard_promise in *; eauto with not_access. eapply nacc_ref.
  - intros ?. subst. sigma. discriminate.
  - sigma. eauto with not_access.
Qed.

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

Local Lemma gp_preservation_write : forall m t1 t2 ad t T,
  guard_promise m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  guard_promise m t2.
Proof.
  intros. ind_tstep; intros until 2; repeat invc_gp;
  unfold guard_promise in *; eauto with not_access.
Qed.

Local Lemma gp_preservation_acq : forall m t1 t2 ad t,
  guard_promise m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  guard_promise m t2.
Proof.
  intros. ind_tstep; intros until 2; repeat invc_gp;
  unfold guard_promise in *; eauto with not_access.
Qed.

Local Lemma gp_preservation_rel : forall m t1 t2 ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t1 ->
  safe_boundaries t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_rel ad]--> t2 ->
  guard_promise m t2.
Proof.
  intros.
  ind_tstep; intros until 2; invc_vr; invc_sb; invc_gp;
  try solve [unfold guard_promise in *; eauto with not_access].
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
  well_typed_term t1 ->
  valid_references m1 t1 ->
  (* --- *)
  guard_promise m1 t1 ->
  m1 / t1 ==[e]==> m2 / t2 ->
  guard_promise m2 t2.
Proof.
  intros. invc_mstep;
  eauto using gp_preservation_none;
  eauto using gp_preservation_alloc;
  eauto using gp_preservation_read;
  eauto using gp_preservation_write;
  eauto using gp_preservation_acq;
  eauto using gp_preservation_rel;
  eauto using gp_preservation_spawn.
Qed.

Theorem gp_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (valid_references m1) ->
  (* --- *)
  forall_threads ths1 (guard_promise m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (guard_promise m2).
Proof.
  intros. invc_cstep; try invc_mstep; intros ?; omicron; eauto;
  eauto using gp_preservation_none;
  eauto using gp_preservation_alloc;
  eauto using gp_preservation_read;
  eauto using gp_preservation_write;
  eauto using gp_preservation_acq;
  eauto using gp_preservation_rel;
  eauto using gp_preservation_spawn.
Qed.


