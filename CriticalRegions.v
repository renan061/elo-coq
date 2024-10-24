From Coq Require Import Lia.

From Elo Require Import Core.

From Elo Require Import ValidReferences.

(* ------------------------------------------------------------------------- *)
(* no-cr(s)                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive no_cr (ad : addr) : tm -> Prop :=
  | nocr_unit  :                no_cr ad <{unit      }>
  | nocr_nat   : forall n,      no_cr ad <{nat n     }>
  | nocr_var   : forall x,      no_cr ad <{var x     }>
  | nocr_fun   : forall x Tx t, no_cr ad t  ->
                                no_cr ad <{fn x Tx t }>
  | nocr_call  : forall t1 t2,  no_cr ad t1 ->
                                no_cr ad t2 ->
                                no_cr ad <{call t1 t2}>
  | nocr_ref   : forall ad' T,  no_cr ad <{&ad' : T  }>
  | nocr_new   : forall T t,    no_cr ad t  ->
                                no_cr ad <{new t : T }>
  | nocr_load  : forall t,      no_cr ad t  ->
                                no_cr ad <{*t        }>
  | nocr_asg   : forall t1 t2,  no_cr ad t1 ->
                                no_cr ad t2 ->
                                no_cr ad <{t1 := t2  }>
  | nocr_acq   : forall t1 t2,  no_cr ad t1 ->
                                no_cr ad t2 ->
                                no_cr ad <{acq t1 t2 }>
  | nocr_cr    : forall ad' t,  ad <> ad'   ->
                                no_cr ad t  ->
                                no_cr ad <{cr ad' t  }>
  | nocr_spawn : forall t,      no_cr ad t  ->
                                no_cr ad <{spawn t   }>
  .

Definition no_crs (t : tm) := forall ad, no_cr ad t.

(* inversion -- no-cr(s) --------------------------------------------------- *)

Local Ltac _nocr tt :=
  match goal with
  | H : no_cr _   <{unit     }> |- _ => clear H
  | H : no_cr _   <{nat _    }> |- _ => clear H
  | H : no_cr _   <{var _    }> |- _ => clear H
  | H : no_cr _   <{fn _ _ _ }> |- _ => tt H
  | H : no_cr _   <{call _ _ }> |- _ => tt H
  | H : no_cr _   <{&_ : _   }> |- _ => clear H
  | H : no_cr _   <{new _ : _}> |- _ => tt H
  | H : no_cr _   <{* _      }> |- _ => tt H
  | H : no_cr _   <{_ := _   }> |- _ => tt H
  | H : no_cr _   <{acq _ _  }> |- _ => tt H
  | H : no_cr ?ad <{cr ?ad _ }> |- _ => invc H; eauto
  | H : no_cr _   <{cr _ _   }> |- _ => tt H
  | H : no_cr _   <{spawn _  }> |- _ => tt H
  end.

Ltac inv_nocr  := _nocr inv.
Ltac invc_nocr := _nocr invc.

Local Ltac solve_inv_nocrs :=
  unfold no_crs; intros * H; try split;
  intros **; auto_specialize; invc_nocr; eauto.

Local Lemma inv_nocrs_fun : forall x Tx t,
  no_crs <{fn x Tx t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_call : forall t1 t2,
  no_crs <{call t1 t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_new : forall t T,
  no_crs <{new t : T}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_load : forall t,
  no_crs <{*t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_asg : forall t1 t2,
  no_crs <{t1 := t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_acq : forall t1 t2,
  no_crs <{acq t1 t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_cr : forall ad t,
  no_crs <{cr ad t}> -> False.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_spawn : forall t,
  no_crs <{spawn t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Ltac invc_nocrs :=
  match goal with
  | H : no_crs <{unit     }> |- _ => clear H
  | H : no_crs <{nat _    }> |- _ => clear H
  | H : no_crs <{var _    }> |- _ => clear H
  | H : no_crs <{fn _ _ _ }> |- _ => eapply inv_nocrs_fun    in H
  | H : no_crs <{call _ _ }> |- _ => eapply inv_nocrs_call   in H as [? ?]
  | H : no_crs <{& _ : _  }> |- _ => clear H
  | H : no_crs <{new _ : _}> |- _ => eapply inv_nocrs_new    in H
  | H : no_crs <{* _      }> |- _ => eapply inv_nocrs_load   in H
  | H : no_crs <{_ := _   }> |- _ => eapply inv_nocrs_asg    in H as [? ?]
  | H : no_crs <{acq _ _  }> |- _ => eapply inv_nocrs_acq    in H as [? ?]
  | H : no_crs <{cr _ _   }> |- _ => contradict H; eauto using inv_nocrs_cr
  | H : no_crs <{spawn _  }> |- _ => eapply inv_nocrs_spawn  in H
  end.

(* lemmas -- no-cr(s) ------------------------------------------------------ *)

Local Corollary nocrs_then_nocr : forall ad t,
  no_crs t ->
  no_cr ad t.
Proof.
  eauto.
Qed.

Local Lemma nocr_from_vr_eq : forall m t,
  valid_references m t ->
  no_cr (#m) t.
Proof.
  intros. induction t; try invc_vr;
  eauto using PeanoNat.Nat.lt_neq, not_eq_sym, no_cr.
Qed.

Local Lemma nocr_from_vr_gt : forall m t ad,
  (#m) < ad ->
  valid_references m t ->
  no_cr ad t.
Proof.
  intros. induction t; try invc_vr; eauto using no_cr.
  match goal with
  |- no_cr ?ad1 <{cr ?ad2 _}> => destruct (nat_eq_dec ad1 ad2); subst
  end.
  - lia.
  - eauto using no_cr.
Qed.

Local Lemma nocr_then_not_rel : forall t1 t2 ad,
  no_cr ad t1 ->
  t1 --[e_rel ad]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_nocr; eauto.
Qed.

(* preservation (no-cr) ---------------------------------------------------- *)

Local Lemma nocr_subst : forall ad x tx t,
  no_cr ad t ->
  no_cr ad tx ->
  no_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; simpl in *; trivial;
  try (destruct str_eq_dec; subst); trivial;
  invc_nocr; eauto using no_cr.
Qed.

Local Corollary nocrs_subst : forall x tx t,
  no_crs t ->
  no_crs tx ->
  no_crs <{[x := tx] t}>.
Proof.
  intros ** ?. eauto using nocr_subst.
Qed.

Local Ltac solve_nocr_preservation :=
  intros; ind_tstep; repeat invc_nocr; eauto using nocr_subst, no_cr.

Local Lemma nocr_preservation_none : forall t1 t2 ad,
  no_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_alloc : forall t1 t2 ad ad' t T,
  no_cr ad t1 ->
  t1 --[e_alloc ad' t T]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_read : forall t1 t2 ad ad' t,
  no_cr ad t ->
  (* --- *)
  no_cr ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_write : forall t1 t2 ad ad' t T,
  no_cr ad t1 ->
  t1 --[e_write ad' t T]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_acq_eq : forall t1 t2 ad t,
  no_cr ad t ->
  (* --- *)
  no_cr ad t1 ->
  t1 --[e_acq ad t]--> t2 ->
  no_cr ad t2 ->
  False.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_acq : forall t1 t2 ad ad' t,
  no_cr ad t ->
  (* --- *)
  ad <> ad' ->
  no_cr ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_rel_neq : forall t1 t2 ad ad',
  ad <> ad' ->
  no_cr ad' t1 ->
  t1 --[e_rel ad]--> t2 ->
  no_cr ad' t2.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_spawn : forall t1 t2 ad tid t,
  no_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_spawned : forall t1 t2 ad tid t,
  no_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_cr ad t.
Proof. solve_nocr_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* valid-crs                                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive valid_crs : tm -> Prop :=
  | vcrs_unit  :                valid_crs <{unit      }>
  | vcrs_nat   : forall n,      valid_crs <{nat n     }>
  | vcrs_var   : forall x,      valid_crs <{var x     }>
  | vcrs_fun   : forall x Tx t, no_crs t     ->
                                valid_crs <{fn x Tx t }>
  | vcrs_call  : forall t1 t2,  valid_crs t1 ->
                                valid_crs t2 ->
                                valid_crs <{call t1 t2}>
  | vcrs_ref   : forall ad T,   valid_crs <{&ad : T   }>
  | vcrs_new   : forall T t,    valid_crs t  ->
                                valid_crs <{new t : T }>
  | vcrs_load  : forall t,      valid_crs t  ->
                                valid_crs <{*t        }>
  | vcrs_asg   : forall t1 t2,  valid_crs t1 ->
                                valid_crs t2 ->
                                valid_crs <{t1 := t2  }>
  | vcrs_acq   : forall t1 t2,  valid_crs t1 ->
                                valid_crs t2 ->
                                valid_crs <{acq t1 t2 }>
  | vcrs_cr    : forall ad t,   valid_crs t  ->
                                valid_crs <{cr ad t   }>
  | vcrs_spawn : forall t,      no_crs t     ->
                                valid_crs <{spawn t   }>
  .

(* inversion -- valid-crs -------------------------------------------------- *)

Local Ltac _vcrs tt :=
  match goal with
  | H : valid_crs <{unit     }> |- _ => clear H
  | H : valid_crs <{nat _    }> |- _ => clear H
  | H : valid_crs <{var _    }> |- _ => clear H
  | H : valid_crs <{fn _ _ _ }> |- _ => tt H
  | H : valid_crs <{call _ _ }> |- _ => tt H
  | H : valid_crs <{&_ : _   }> |- _ => clear H
  | H : valid_crs <{new _ : _}> |- _ => tt H
  | H : valid_crs <{* _      }> |- _ => tt H
  | H : valid_crs <{_ := _   }> |- _ => tt H
  | H : valid_crs <{acq _ _  }> |- _ => tt H
  | H : valid_crs <{cr _ _   }> |- _ => tt H
  | H : valid_crs <{spawn _  }> |- _ => tt H
  end.

Ltac inv_vcrs  := _vcrs inv.
Ltac invc_vcrs := _vcrs invc.

(* lemmas -- valid-crs ----------------------------------------------------- *)

Lemma nocrs_then_vcrs : forall t,
  no_crs t ->
  valid_crs t.
Proof.
  intros. induction t; invc_nocrs; eauto using valid_crs.
Qed.

Lemma value_then_nocr : forall ad t,
  valid_crs t ->
  value t ->
  no_cr ad t.
Proof.
  intros * ? Hval. invc Hval; invc_vcrs; eauto using no_cr.
Qed.

Corollary value_then_nocrs : forall t,
  valid_crs t ->
  value  t ->
  no_crs t.
Proof.
  intros ** ?. eauto using value_then_nocr.
Qed.

Corollary mem_then_nocrs : forall m,
  forall_memory m value ->
  forall_memory m valid_crs ->
  forall_memory m no_crs.
Proof.
  intros ** ?. eauto using value_then_nocrs.
Qed.

Local Lemma vcrs_alloc_term : forall t1 t2 ad t T,
  valid_crs t1 ->
  t1 --[e_alloc ad t T]--> t2 ->
  valid_crs t.
Proof.
  intros. ind_tstep; invc_vcrs; eauto using nocrs_then_vcrs.
Qed.

Local Lemma vcrs_write_term  : forall t1 t2 ad t T,
  valid_crs t1 ->
  t1 --[e_write ad t T]--> t2 ->
  valid_crs t.
Proof.
  intros. ind_tstep; invc_vcrs; eauto using nocrs_then_vcrs.
Qed.

Local Lemma nocrs_spawn_term : forall t1 t2 tid t,
  valid_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_crs t.
Proof. 
  intros. ind_tstep; invc_vcrs; eauto.
Qed.

(* preservation -- valid-crs ----------------------------------------------- *)

Local Ltac solve_vcrs_preservation :=
  intros; ind_tstep; repeat invc_vcrs; eauto using valid_crs;
  eauto using nocrs_then_vcrs, nocrs_subst, value_then_nocrs, valid_crs.

Local Lemma vcrs_preservation_none : forall t1 t2,
  valid_crs t1 ->
  t1 --[e_none]--> t2 ->
  valid_crs t2.
Proof. solve_vcrs_preservation. Qed.

Local Lemma vcrs_preservation_alloc : forall t1 t2 ad t T,
  valid_crs t1 ->
  t1 --[e_alloc ad t T]--> t2 ->
  valid_crs t2.
Proof. solve_vcrs_preservation. Qed.

Local Lemma vcrs_preservation_read : forall t1 t2 ad t,
  no_crs t ->
  (* --- *)
  valid_crs t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_crs t2.
Proof. solve_vcrs_preservation. Qed.

Local Lemma vcrs_preservation_write : forall t1 t2 ad t T,
  valid_crs t1 ->
  t1 --[e_write ad t T]--> t2 ->
  valid_crs t2.
Proof. solve_vcrs_preservation. Qed.

Local Lemma vcrs_preservation_acq : forall t1 t2 ad t,
  no_crs t ->
  (* --- *)
  valid_crs t1 ->
  t1 --[e_acq ad t]--> t2 ->
  valid_crs t2.
Proof. solve_vcrs_preservation. Qed.

Local Lemma vcrs_preservation_rel : forall t1 t2 ad,
  valid_crs t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_crs t2.
Proof. solve_vcrs_preservation. Qed.

Local Lemma vcrs_preservation_spawn : forall t1 t2 tid t,
  valid_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_crs t2.
Proof. solve_vcrs_preservation. Qed.

Local Lemma vcrs_preservation_tm_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_crs ->
  (* --- *)
  forall_threads ths1 valid_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 valid_crs.
Proof.
  intros ** ?. invc_cstep; try invc_mstep; omicron; eauto using valid_crs;
  eauto using vcrs_preservation_none;
  eauto using vcrs_preservation_alloc;
  eauto using vcrs_preservation_read;
  eauto using vcrs_preservation_write;
  eauto using vcrs_preservation_acq;
  eauto using vcrs_preservation_rel;
  eauto using vcrs_preservation_spawn;
  eauto using nocrs_spawn_term, nocrs_then_vcrs.
Qed.

Local Lemma vcrs_preservation_mem_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 valid_crs ->
  (* --- *)
  forall_memory m1 valid_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory m2 valid_crs.
Proof.
  intros ** ?. invc_cstep; try invc_mstep; trivial; omicron; eauto;
  eauto using vcrs_alloc_term;
  eauto using valid_crs;
  eauto using vcrs_write_term.
Qed.

Theorem vcrs_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_crs ->
  (* --- *)
  forall_program m1 ths1 valid_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 valid_crs.
Proof.
  intros * ? [? ?] **. split;
  eauto using vcrs_preservation_tm_cstep, vcrs_preservation_mem_cstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-cr                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive one_cr (ad : addr) : tm -> Prop :=
  | onecr_call1  : forall t1 t2,  one_cr ad t1 ->
                                  no_cr  ad t2 ->
                                  one_cr ad <{call t1 t2}>
  | onecr_call2  : forall t1 t2,  no_cr  ad t1 ->
                                  one_cr ad t2 ->
                                  one_cr ad <{call t1 t2}>
  | onecr_new    : forall T t,    one_cr ad t  ->
                                  one_cr ad <{new t : T }>
  | onecr_load   : forall t,      one_cr ad t  ->
                                  one_cr ad <{*t        }>
  | onecr_asg1   : forall t1 t2,  one_cr ad t1 ->
                                  no_cr  ad t2 ->
                                  one_cr ad <{t1 := t2  }>
  | onecr_asg2   : forall t1 t2,  no_cr  ad t1 ->
                                  one_cr ad t2 ->
                                  one_cr ad <{t1 := t2  }>
  | onecr_acq1   : forall t1 t2,  one_cr ad t1 ->
                                  no_cr  ad t2 ->
                                  one_cr ad <{acq t1 t2 }>
  | onecr_acq2   : forall t1 t2,  no_cr  ad t1 ->
                                  one_cr ad t2 ->
                                  one_cr ad <{acq t1 t2 }>
  | onecr_cr_eq  : forall t,      no_cr  ad t  ->
                                  one_cr ad <{cr ad t   }>
  | onecr_cr_neq : forall ad' t,  ad <> ad'    ->
                                  one_cr ad t  ->
                                  one_cr ad <{cr ad' t  }>
  .

(* inversion -- one-cr ----------------------------------------------------- *)

Local Ltac _onecr tt :=
  match goal with
  | H : one_cr _ <{unit     }> |- _ => inv H
  | H : one_cr _ <{nat _    }> |- _ => inv H
  | H : one_cr _ <{var _    }> |- _ => inv H
  | H : one_cr _ <{fn _ _ _ }> |- _ => inv H
  | H : one_cr _ <{call _ _ }> |- _ => tt H
  | H : one_cr _ <{&_ : _   }> |- _ => inv H
  | H : one_cr _ <{new _ : _}> |- _ => tt H
  | H : one_cr _ <{* _      }> |- _ => tt H
  | H : one_cr _ <{_ := _   }> |- _ => tt H
  | H : one_cr _ <{acq _ _  }> |- _ => tt H
  | H : one_cr _ <{cr _ _   }> |- _ => tt H
  | H : one_cr _ <{spawn _  }> |- _ => inv H
  end.

Ltac inv_onecr  := _onecr inv.
Ltac invc_onecr := _onecr invc.

(* lemmas -- one-cr -------------------------------------------------------- *)

Local Lemma nocrs_then_not_onecr : forall ad t,
  no_crs t ->
  one_cr ad t ->
  False.
Proof.
  intros * H ?. specialize (H ad).
  induction t; invc_nocr; invc_onecr; eauto using one_cr.
Qed.

Local Lemma nocr_acq_to_onecr : forall t1 t2 ad t,
  no_crs t ->
  (* --- *)
  no_cr ad t1 ->
  t1 --[e_acq ad t]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_nocr; eauto using one_cr, nocr_subst.
Qed.

Local Lemma onecr_rel_to_nocr : forall t1 t2 ad,
  one_cr ad t1 ->
  t1 --[e_rel ad]--> t2 ->
  no_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_onecr; eauto using no_cr;
  exfalso; eauto using nocr_then_not_rel.
Qed.

(* preservation -- one-cr -------------------------------------------------- *)

Local Lemma onecr_subst : forall ad x tx t,
  no_cr  ad tx -> 
  one_cr ad t  ->
  one_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_onecr; eauto using nocr_subst, one_cr; simpl in *;
  destruct str_eq_dec; subst; eauto using one_cr.
Qed.

Local Lemma onecr_preservation_none : forall t1 t2 ad,
  valid_crs t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_vcrs; repeat invc_onecr;
  eauto using nocr_preservation_none, onecr_subst, one_cr.
  invc_nocr. exfalso. eauto using value_then_nocrs, nocrs_then_not_onecr.
Qed.

Local Lemma onecr_preservation_alloc : forall t1 t2 ad ad' t T,
  valid_crs t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_alloc ad' t T]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; invc_vcrs; invc_onecr;
  eauto using nocr_preservation_alloc, one_cr.
  exfalso. eauto using value_then_nocrs, nocrs_then_not_onecr.
Qed.

Local Lemma onecr_preservation_read : forall t1 t2 ad ad' t,
  no_crs t ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_onecr;
  eauto using nocr_preservation_read, one_cr.
Qed.

Local Lemma onecr_preservation_write : forall t1 t2 ad ad' t T,
  valid_crs t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_write ad' t T]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_vcrs; invc_onecr;
  eauto using nocr_preservation_write, one_cr.
  - invc_onecr.
  - exfalso. eauto using value_then_nocrs, nocrs_then_not_onecr.
Qed.

Local Lemma onecr_preservation_acq : forall t1 t2 ad ad' t,
  no_cr ad t ->
  (* --- *)
  ad <> ad' ->
  one_cr ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_onecr;
  eauto using nocr_preservation_acq, one_cr.
Qed.

Local Lemma onecr_preservation_rel : forall t1 t2 ad ad',
  ad <> ad' ->
  one_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_onecr;
  eauto using nocr_preservation_rel_neq, one_cr.
Qed.

Local Lemma onecr_preservation_spawn : forall ad t1 t2 tid t,
  valid_crs t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; invc_vcrs; invc_onecr;
  eauto using nocr_preservation_spawn, one_cr.
Qed.

(* ------------------------------------------------------------------------- *)
(* unique-critical-regions                                                   *)
(* ------------------------------------------------------------------------- *)

Definition locked_then_nocrs (m : mem) (ths : threads) :=
  forall ad, m[ad].X = false -> forall tid, no_cr ad ths[tid].

Definition unlocked_then_onecr (m : mem) (ths : threads) :=
  forall ad, m[ad].X = true ->
    exists tid, one_cr ad ths[tid] /\
    forall tid', tid <> tid' -> no_cr ad ths[tid'].

Definition unique_critical_regions (m : mem) (ths : threads) :=
  locked_then_nocrs m ths /\ unlocked_then_onecr m ths.

(* preservation -- unique-critical-regions --------------------------------- *)

Local Lemma ucr_preservation_none : forall m ths tid t,
  forall_threads ths valid_crs ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_none]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros until 2. intros [? Hunlocked] ?. split; intros ad Had **.
  - omicron; eauto using nocr_preservation_none.
  - specialize (Hunlocked ad Had) as [tid' [? ?]]. exists tid'.
    omicron; split; eauto using onecr_preservation_none; intros. 
    + sigma. eauto.
    + omicron; eauto using nocr_preservation_none.
Qed.

Local Lemma ucr_preservation_alloc : forall m ths tid t te Te,
  forall_threads ths (valid_references m) ->
  forall_threads ths valid_crs ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_alloc (#m) te Te]--> t ->
  unique_critical_regions (m +++ (te, Te, false)) ths[tid <- t].
Proof.
  intros until 3. intros [? Hunlocked] ?.
  split; intros ad Had **; repeat omicron;
  eauto using nocr_from_vr_eq, nocr_from_vr_gt, nocr_preservation_alloc.
  specialize (Hunlocked ad Had) as [tid' [? ?]]. exists tid'.
  split; intros; omicron;
  eauto using nocr_preservation_alloc, onecr_preservation_alloc.
Qed.

Local Lemma ucr_preservation_read : forall m ths tid t ad te,
  no_crs te ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros * ? ? [Hucr1 Hucr2] ?. split; intros ad' Had' **.
  - omicron; eauto using nocr_preservation_read.
  - specialize (Hucr2 ad' Had') as [tid' [? ?]]. exists tid'.
    omicron; split; eauto using onecr_preservation_read; intros. 
    + sigma. eauto.
    + omicron; eauto using nocr_preservation_read.
Qed.

Local Lemma ucr_preservation_write : forall m ths tid t ad te Te,
  forall_threads ths (valid_references m) ->
  forall_threads ths valid_crs ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_write ad te Te]--> t ->
  unique_critical_regions m[ad.tT <- te Te] ths[tid <- t].
Proof.
  intros until 3. intros [? Hunlocked] ?.
  assert (ad < #m) by eauto using vr_tstep_write_addr.
  split; intros ad' Had' **; repeat omicron;
  eauto using nocr_preservation_write;
  specialize (Hunlocked ad' Had') as [tid' [? ?]];
  exists tid'; split; intros; omicron;
  eauto using nocr_preservation_write, onecr_preservation_write.
Qed.

Local Lemma ucr_preservation_acq : forall m ths tid ad t te,
  no_crs te ->
  (* --- *)
  ad < #m ->
  tid < #ths ->
  m[ad].X = false ->
  unique_critical_regions m ths ->
  ths[tid] --[e_acq ad te]--> t ->
  unique_critical_regions m[ad.X <- true] ths[tid <- t].
Proof.
  intros until 4. intros [? Hunlocked] ?.
  split; intros ad' Had' **; repeat omicron;
  eauto using nocr_preservation_acq.
  - exists tid. sigma. split.
    + eauto using nocr_acq_to_onecr.
    + intros. sigma. eauto.
  - specialize (Hunlocked ad' Had') as [tid' [? ?]]. exists tid'. split.
    + omicron; eauto using onecr_preservation_acq.
    + intros. omicron; eauto using nocr_preservation_acq.
Qed.

Local Lemma ucr_preservation_rel : forall m ths tid ad t,
  ad < #m ->
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_critical_regions m[ad.X <- false] ths[tid <- t].
Proof.
  intros until 2. intros [? Hunlocked] ?.
  assert (Had : m[ad].X = true). { (* This is cool *)
    destruct (m[ad].X) eqn:Heq; trivial. exfalso.
    eauto using nocr_then_not_rel.
  } 
  split; intros ad' Had'; try intros tid';
  repeat omicron; eauto using nocr_preservation_rel_neq.
  - specialize (Hunlocked ad' Had) as [tid'' [? ?]].
    destruct (nat_eq_dec tid'' tid'); subst; eauto using onecr_rel_to_nocr.
    exfalso. eauto using nocr_then_not_rel.
  - specialize (Hunlocked ad' Had) as [tid'' [? ?]].
    destruct (nat_eq_dec tid'' tid'); subst;
    eauto using nocr_then_not_rel.
  - specialize (Hunlocked ad' Had') as [tid' [? ?]]. exists tid'.
    destruct (nat_eq_dec tid' tid); subst; sigma;
    split; eauto using onecr_preservation_rel; intros.
    + sigma. eauto.
    + omicron; eauto using nocr_preservation_rel_neq.
Qed.

Local Ltac eapply_in_tstep tt :=
  match goal with Htstep : _ --[_]--> _ |- _ => eapply tt in Htstep as ? end.

Local Lemma ucr_preservation_spawn : forall m ths tid t te,
  forall_threads ths valid_crs ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  unique_critical_regions m (ths[tid <- t] +++ te).
Proof.
  intros until 2. intros [? Hunlocked] ?. split; intros ad Had **.
  - omicron; eauto using no_cr.
    + eapply_in_tstep nocr_preservation_spawn; eauto using no_cr.
    + eauto using nocr_preservation_spawned.
  - specialize (Hunlocked ad Had) as [tid' [? ?]]. exists tid'. omicron;
    try invc_onecr; split; eauto using onecr_preservation_spawn; intros;
    omicron; eauto using no_cr.
    + eapply_in_tstep nocrs_spawn_term; eauto.
    + eauto using nocr_preservation_spawn.
    + eapply_in_tstep nocrs_spawn_term; eauto.
Qed.

Theorem ucr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_crs ->
  forall_threads ths1 (valid_references m1) ->
  forall_threads ths1 valid_crs ->
  (* --- *)
  unique_critical_regions m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  unique_critical_regions m2 ths2.
Proof.
  intros. invc_cstep; try invc_mstep;
  eauto using ucr_preservation_none; 
  eauto using ucr_preservation_alloc; 
  eauto using ucr_preservation_read; 
  eauto using ucr_preservation_write; 
  eauto using ucr_preservation_acq; 
  eauto using ucr_preservation_rel;
  eauto using ucr_preservation_spawn.
Qed.

