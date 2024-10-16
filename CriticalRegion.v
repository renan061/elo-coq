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

Corollary nocrs_then_nocr : forall ad t,
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

Local Lemma nocr_preservation_acq_neq : forall t1 t2 ad ad' t,
  no_cr ad t ->
  (* --- *)
  ad <> ad' ->
  no_cr ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Local Lemma nocr_preservation_rel_eq : forall t1 t2 ad,
  no_cr ad t1 ->
  t1 --[e_rel ad]--> t2 ->
  False.
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
(* ok-crs                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive ok_crs : tm -> Prop :=
  | okcrs_unit   :                ok_crs <{unit      }>
  | okcrs_nat    : forall n,      ok_crs <{nat n     }>
  | okcrs_var    : forall x,      ok_crs <{var x     }>
  | okcrs_fun    : forall x Tx t, no_crs t  ->
                                  ok_crs <{fn x Tx t }>
  | okcrs_call1  : forall t1 t2,  ~ value t1 ->
                                  ok_crs  t1 ->
                                  no_crs  t2 ->
                                  ok_crs <{call t1 t2}>
  | okcrs_call2  : forall t1 t2,  value   t1 ->
                                  ~ value t2 ->
                                  no_crs  t1 ->
                                  ok_crs  t2 ->
                                  ok_crs <{call t1 t2}>
  | okcrs_call3  : forall t1 t2,  value   t1 ->
                                  value   t2 ->
                                  no_crs  t1 ->
                                  no_crs  t2 ->
                                  ok_crs <{call t1 t2}>
  | okcrs_ref    : forall ad' T,  ok_crs <{&ad' : T  }>
  | okcrs_new    : forall T t,    ok_crs t   ->
                                  ok_crs <{new t : T }>
  | okcrs_load   : forall t,      ok_crs t   ->
                                  ok_crs <{*t        }>
  | okcrs_asg1   : forall t1 t2,  ~ value t1 ->
                                  ok_crs  t1 ->
                                  no_crs  t2 ->
                                  ok_crs <{t1 := t2  }>
  | okcrs_asg2   : forall t1 t2,  value   t1 ->
                                  ~ value t2 ->
                                  no_crs  t1 ->
                                  ok_crs  t2 ->
                                  ok_crs <{t1 := t2  }>
  | okcrs_asg3  : forall t1 t2,   value   t1 ->
                                  value   t2 ->
                                  no_crs  t1 ->
                                  no_crs  t2 ->
                                  ok_crs <{t1 := t2  }>
  | okcrs_acq1  : forall t1 t2,   ~ value t1 ->
                                  ok_crs  t1 ->
                                  no_crs  t2 ->
                                  ok_crs <{acq t1 t2 }>
  | okcrs_acq2  : forall t1 t2,   value   t1 ->
                                  ~ value t2 ->
                                  no_crs  t1 ->
                                  ok_crs  t2 ->
                                  ok_crs <{acq t1 t2 }>
  | okcrs_acq3  : forall t1 t2,   value   t1 ->
                                  value   t2 ->
                                  no_crs  t1 ->
                                  no_crs  t2 ->
                                  ok_crs <{acq t1 t2 }>
  | okcrs_cr    : forall ad t,    ok_crs t   ->
                                  ok_crs <{cr ad t   }>
  | okcrs_spawn : forall t,       no_crs t   ->
                                  ok_crs <{spawn t   }>
  .

(* inversion -- ok-crs ----------------------------------------------------- *)

Local Ltac _okcrs tt :=
  match goal with
  | H : ok_crs <{unit     }> |- _ => clear H
  | H : ok_crs <{nat _    }> |- _ => clear H
  | H : ok_crs <{var _    }> |- _ => clear H
  | H : ok_crs <{fn _ _ _ }> |- _ => tt H
  | H : ok_crs <{call _ _ }> |- _ => tt H
  | H : ok_crs <{&_ : _   }> |- _ => clear H
  | H : ok_crs <{new _ : _}> |- _ => tt H
  | H : ok_crs <{* _      }> |- _ => tt H
  | H : ok_crs <{_ := _   }> |- _ => tt H
  | H : ok_crs <{acq _ _  }> |- _ => tt H
  | H : ok_crs <{cr _ _   }> |- _ => tt H
  | H : ok_crs <{spawn _  }> |- _ => tt H
  end.

Ltac inv_okcrs  := _okcrs inv.
Ltac invc_okcrs := _okcrs invc.

(* lemmas -- ok-crs -------------------------------------------------------- *)

Lemma nocrs_then_okcrs : forall t,
  no_crs t ->
  ok_crs t.
Proof.
  intros. induction t; invc_nocrs; eauto using ok_crs;
  destruct (value_dec t1), (value_dec t2); eauto using ok_crs.
Qed.

Lemma value_then_nocr : forall ad t,
  ok_crs t ->
  (* --- *)
  value t ->
  no_cr ad t.
Proof.
  intros * ? Hval. invc Hval; invc_okcrs; eauto using no_cr.
Qed.

Corollary value_then_nocrs : forall t,
  ok_crs t ->
  (* --- *)
  value  t ->
  no_crs t.
Proof.
  intros ** ?. eauto using value_then_nocr.
Qed.

(* preservation -- ok-crs -------------------------------------------------- *)

Local Corollary nocrs_subst : forall x tx t,
  no_crs t ->
  no_crs tx ->
  no_crs <{[x := tx] t}>.
Proof.
  intros ** ?. eauto using nocr_subst.
Qed.

Local Lemma okcrs_subst : forall x tx t,
  value  tx ->
  no_crs t ->
  ok_crs tx ->
  ok_crs <{[x := tx] t}>.
Proof.
  intros. induction t; simpl in *; invc_nocrs;
  try (destruct str_eq_dec); eauto using value_then_nocrs, nocrs_subst, ok_crs;
  repeat auto_specialize;
  destruct (value_dec <{[x := tx] t1}>), (value_dec <{[x := tx] t2}>);
  eauto using value_then_nocrs, nocrs_subst, ok_crs.
Qed.

Local Lemma value_does_not_step : forall t1 t2 e,
  value t1 ->
  t1 --[e]--> t2 ->
  False.
Proof.
  intros * Hval ?. ind_tstep; invc Hval.
Qed.

Local Ltac solve_okcrs_preservation :=
  intros; ind_tstep; invc_okcrs;
  eauto using ok_crs,
    nocr_preservation_none,
    nocr_preservation_alloc,
    nocr_preservation_read,
    nocr_preservation_write,
    nocr_preservation_spawn;
  solve [ invc_nocrs; eauto using nocrs_then_okcrs, okcrs_subst, ok_crs
        | exfalso; eauto using value_does_not_step, value
        | match goal with
          |- ok_crs (_ ?t1 ?t2) =>
            destruct (value_dec t1), (value_dec t2);
            eauto using value_then_nocrs, nocrs_then_okcrs, ok_crs
          end
        ].

Local Lemma okcrs_preservation_none : forall t1 t2,
  ok_crs t1 ->
  t1 --[e_none]--> t2 ->
  ok_crs t2.
Proof. solve_okcrs_preservation. Qed.

Local Lemma okcrs_preservation_alloc : forall t1 t2 ad t T,
  ok_crs t1 ->
  t1 --[e_alloc ad t T]--> t2 ->
  ok_crs t2.
Proof. solve_okcrs_preservation. Qed.

Local Lemma okcrs_preservation_read : forall t1 t2 ad t,
  ok_crs t ->
  (* --- *)
  ok_crs t1 ->
  t1 --[e_read ad t]--> t2 ->
  ok_crs t2.
Proof. solve_okcrs_preservation. Qed.

Local Lemma okcrs_preservation_write : forall t1 t2 ad t T,
  ok_crs t1 ->
  t1 --[e_write ad t T]--> t2 ->
  ok_crs t2.
Proof. solve_okcrs_preservation. Qed.

Local Lemma okcrs_preservation_acq : forall t1 t2 ad t,
  value  t ->
  ok_crs t ->
  (* --- *)
  ok_crs t1 ->
  t1 --[e_acq ad t]--> t2 ->
  ok_crs t2.
Proof. solve_okcrs_preservation. Qed.

Local Lemma okcrs_preservation_rel : forall t1 t2 ad,
  ok_crs t1 ->
  t1 --[e_rel ad]--> t2 ->
  ok_crs t2.
Proof. solve_okcrs_preservation. Qed.

Local Lemma okcrs_preservation_spawn : forall t1 t2 tid t,
  ok_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  ok_crs t2.
Proof. solve_okcrs_preservation. Qed.

Local Lemma okcrs_preservation_spawned : forall t1 t2 tid t,
  ok_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_crs t.
Proof.
  intros. ind_tstep; invc_okcrs; eauto;
  exfalso; eauto using value_does_not_step.
Qed.

Local Lemma okcrs_preservation_tm_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_memory m1 ok_crs ->
  (* --- *)
  forall_threads ths1 ok_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 ok_crs.
Proof.
  intros * ? ? H ? tid' **.
  invc_cstep; try invc_mstep; omicron; eauto using ok_crs;
  eauto using okcrs_preservation_none;
  eauto using okcrs_preservation_alloc;
  eauto using okcrs_preservation_read;
  eauto using okcrs_preservation_write;
  eauto using okcrs_preservation_acq;
  eauto using okcrs_preservation_rel;
  eauto using okcrs_preservation_spawn;
  eauto using okcrs_preservation_spawned, nocrs_then_okcrs.
Qed.

Local Lemma okcrs_alloc_term : forall t1 t2 ad t T,
  ok_crs t1 ->
  t1 --[e_alloc ad t T]--> t2 ->
  ok_crs t.
Proof.
  intros. ind_tstep; invc_okcrs; eauto using nocrs_then_okcrs.
Qed.

Local Lemma okcrs_write_term  : forall t1 t2 ad t T,
  ok_crs t1 ->
  t1 --[e_write ad t T]--> t2 ->
  ok_crs t.
Proof.
  intros. ind_tstep; invc_okcrs; eauto using nocrs_then_okcrs.
Qed.

Local Lemma okcrs_preservation_mem_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 ok_crs ->
  (* --- *)
  forall_memory m1 ok_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_memory m2 ok_crs.
Proof.
  intros * H ** ?. invc_cstep; try invc_mstep; trivial;
  omicron; eauto using okcrs_alloc_term, okcrs_write_term, ok_crs.
Qed.

Theorem okcrs_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  (* --- *)
  forall_program m1 ths1 ok_crs ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 ok_crs.
Proof.
  intros * ? [? ?] **. split;
  eauto using okcrs_preservation_tm_cstep, okcrs_preservation_mem_cstep.
Qed.

(* ------------------------------------------------------------------------- *)
(* one-cr                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive one_cr (ad : addr) : tm -> Prop :=
  | onecr_fun    : forall x Tx t, one_cr ad t  ->
                                  one_cr ad <{fn x Tx t }>
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
                                  one_cr ad <{cr ad t  }>
  | onecr_cr_neq : forall ad' t,  ad <> ad'    ->
                                  one_cr ad t  ->
                                  one_cr ad <{cr ad' t  }>
  | onecr_spawn  : forall t,      one_cr ad t  ->
                                  one_cr ad <{spawn t   }>
  .

(* inversion -- one-cr ----------------------------------------------------- *)

Local Ltac _onecr tt :=
  match goal with
  | H : one_cr _ <{unit     }> |- _ => inv H
  | H : one_cr _ <{nat _    }> |- _ => inv H
  | H : one_cr _ <{var _    }> |- _ => inv H
  | H : one_cr _ <{fn _ _ _ }> |- _ => tt H
  | H : one_cr _ <{call _ _ }> |- _ => tt H
  | H : one_cr _ <{&_ : _   }> |- _ => inv H
  | H : one_cr _ <{new _ : _}> |- _ => tt H
  | H : one_cr _ <{* _      }> |- _ => tt H
  | H : one_cr _ <{_ := _   }> |- _ => tt H
  | H : one_cr _ <{acq _ _  }> |- _ => tt H
  | H : one_cr _ <{cr _ _   }> |- _ => tt H
  | H : one_cr _ <{spawn _  }> |- _ => tt H
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
  exfalso; eauto using nocr_preservation_rel_eq.
Qed.

(* preservation -- one-cr -------------------------------------------------- *)

Local Lemma onecr_subst : forall ad x tx t,
  no_cr  ad tx -> 
  one_cr ad t ->
  one_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_onecr; eauto using nocr_subst, one_cr; simpl in *;
  destruct str_eq_dec; subst; eauto using one_cr.
Qed.

Local Lemma onecr_preservation_none : forall t1 t2 ad,
  ok_crs t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; invc_okcrs; repeat invc_onecr;
  eauto using nocr_preservation_none, onecr_subst, one_cr;
  exfalso; eauto using value_does_not_step, value, nocrs_then_not_onecr.
Qed.

Local Lemma onecr_preservation_alloc : forall t1 t2 ad ad' t T,
  ok_crs t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_alloc ad' t T]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; invc_okcrs; invc_onecr;
  eauto using nocr_preservation_alloc, one_cr;
  exfalso;
  eauto using value_does_not_step;
  eauto using value_then_nocrs, nocrs_then_not_onecr.
Qed.

Local Lemma onecr_preservation_read : forall t1 t2 ad ad' te,
  no_crs te ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_read ad' te]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_onecr;
  eauto using nocr_preservation_read, one_cr.
Qed.

Local Lemma onecr_preservation_write : forall t1 t2 ad ad' t T,
  ok_crs t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_write ad' t T]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; invc_okcrs; invc_onecr;
  eauto using nocr_preservation_write, one_cr;
  exfalso; eauto using value_does_not_step, value, nocrs_then_not_onecr.
Qed.

Local Lemma onecr_preservation_acq_neq : forall t1 t2 ad ad' t,
  no_cr ad t ->
  (* --- *)
  ad <> ad' ->
  one_cr ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_onecr;
  eauto using nocr_preservation_acq_neq, one_cr.
  eauto using onecr_subst, one_cr.
Qed.

Local Lemma onecr_preservation_rel_neq : forall t1 t2 ad ad',
  ad <> ad' ->
  one_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_onecr;
  eauto using nocr_preservation_rel_neq, one_cr.
Qed.

Local Lemma onecr_preservation_spawn : forall ad t1 t2 tid t,
  ok_crs t1 ->
  (* --- *)
  one_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  one_cr ad t2.
Proof.
  intros. ind_tstep; invc_okcrs; repeat invc_onecr;
  eauto using nocr_preservation_spawn, one_cr;
  exfalso; eauto using value_does_not_step, nocrs_then_not_onecr.
Qed.

(* ------------------------------------------------------------------------- *)
(* unique-critical-regions                                                   *)
(* ------------------------------------------------------------------------- *)

Definition unique_critical_regions1 (m : mem) (ths : threads) :=
  forall ad, m[ad].X = false ->
    forall tid, no_cr ad ths[tid].

Definition unique_critical_regions2 (m : mem) (ths : threads) :=
  forall ad, m[ad].X = true ->
    exists tid, one_cr ad ths[tid] /\
    forall tid', tid <> tid' -> no_cr ad ths[tid'].

Definition unique_critical_regions (m : mem) (ths : threads) :=
  unique_critical_regions1 m ths /\ unique_critical_regions2 m ths.

(* preservation -- unique-critical-regions --------------------------------- *)

Local Lemma ucr_preservation_none : forall m ths tid t,
  forall_threads ths ok_crs ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_none]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros * Hokcrs ? [Hucr1 Hucr2] ?. split.
  - intros ? ? ?. omicron; eauto using nocr_preservation_none.
  - intros ad Had. specialize (Hucr2 ad Had) as [tid' [? ?]]. exists tid'.
    omicron; split; eauto using onecr_preservation_none; intros ? ?. 
    + sigma. eauto.
    + omicron; eauto using nocr_preservation_none.
Qed.

Local Lemma ucr_preservation_alloc : forall m ths tid t te Te,
  forall_threads ths (valid_references m) ->
  forall_threads ths ok_crs ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_alloc (#m) te Te]--> t ->
  unique_critical_regions (m +++ (te, Te, false)) ths[tid <- t].
Proof.
  intros * Hvr ? ? [Hucr1 Hucr2] ?. split; intros ad' Had' **; repeat omicron;
  eauto using nocr_from_vr_eq, nocr_from_vr_gt, nocr_preservation_alloc.
  - specialize (Hucr2 ad' Had') as [tid' [? ?]].
    exists tid'. split; intros; omicron;
    eauto using nocr_preservation_alloc, onecr_preservation_alloc.
  - invc Had'.
  - invc Had'.
Qed.

Local Lemma ucr_preservation_read : forall m ths tid t ad te,
  no_crs te ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_read ad te]--> t ->
  unique_critical_regions m ths[tid <- t].
Proof.
  intros * ? ? [Hucr1 Hucr2] ?. split.
  - intros ? ? ?. omicron; eauto using nocr_preservation_read.
  - intros ad' Had'. specialize (Hucr2 ad' Had') as [tid' [? ?]]. exists tid'.
    omicron; split; eauto using onecr_preservation_read; intros ? ?. 
    + sigma. eauto.
    + omicron; eauto using nocr_preservation_read.
Qed.

Local Lemma ucr_preservation_write : forall m ths tid t ad te Te,
  forall_threads ths (valid_references m) ->
  forall_threads ths ok_crs ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_write ad te Te]--> t ->
  unique_critical_regions m[ad.tT <- te Te] ths[tid <- t].
Proof.
  intros * ? ? ? [Hucr1 Hucr2] ?.
  assert (ad < #m) by eauto using vr_tstep_write_addr.
  split; intros ad' Had' **; repeat omicron;
  eauto using nocr_preservation_write; try solve [invc Had'];
  specialize (Hucr2 ad' Had') as [tid' [? ?]];
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
  intros * ? ? ? Had [Hucr1 Hucr2] ?. split.
  - intros ad' Had' tid'. repeat omicron; eauto.
    assert (no_cr ad' te) by eauto using nocrs_then_nocr.
    eauto using nocr_preservation_acq_neq.
  - intros ad' Had'. omicron.
    + exists tid. sigma. split.
      * eauto using nocr_acq_to_onecr.
      * intros. sigma. eauto.
    + specialize (Hucr2 ad' Had') as [tid' [? ?]]. exists tid'. split.
      * omicron; eauto using onecr_preservation_acq_neq.
      * intros. omicron; eauto using nocr_preservation_acq_neq.
Qed.

Local Lemma ucr_preservation_rel : forall m ths tid ad t,
  ad < #m ->
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_rel ad]--> t ->
  unique_critical_regions m[ad.X <- false] ths[tid <- t].
Proof.
  intros * ? ? [Hucr1 Hucr2] ?.
  assert (Had : m[ad].X = true). {
    destruct (m[ad].X) eqn:Heq; trivial. exfalso.
    eauto using nocr_preservation_rel_eq.
  }
  split.
  - intros ad' ? tid'. repeat omicron; eauto using nocr_preservation_rel_neq.
    + specialize (Hucr2 ad' Had) as [tid'' [? ?]].
      destruct (nat_eq_dec tid'' tid'); subst.
      * eauto using onecr_rel_to_nocr.
      * exfalso. eauto using nocr_preservation_rel_eq.
    + specialize (Hucr2 ad' Had) as [tid'' [? ?]].
      destruct (nat_eq_dec tid'' tid'); subst;
      eauto using nocr_preservation_rel_eq.
  - intros ad' Had'. omicron.
    specialize (Hucr2 ad' Had') as [tid' [? ?]]. exists tid'.
    destruct (nat_eq_dec tid' tid); subst; sigma.
    + split; eauto using onecr_preservation_rel_neq.
      intros ? ?. sigma. eauto.
    + split; eauto.
      intros tid'' ?. omicron; eauto using nocr_preservation_rel_neq.
Qed.

Ltac eapply_tstep tt :=
  match goal with Htstep : _ --[_]--> _ |- _ => eapply tt in Htstep as ? end.

Local Lemma ucr_preservation_spawn : forall m ths tid t te,
  forall_threads ths ok_crs ->
  (* --- *)
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_spawn (#ths) te]--> t ->
  unique_critical_regions m (ths[tid <- t] +++ te).
Proof.
  intros * ? ? [Hucr1 Hucr2] ?. split; intros ad Had **.
  - omicron; eauto using no_cr.
    + eapply_tstep nocr_preservation_spawn; eauto using no_cr.
    + eauto using nocr_preservation_spawned.
  - specialize (Hucr2 ad Had) as [tid' [? ?]]. exists tid'. omicron;
    try invc_onecr; split; eauto using onecr_preservation_spawn.
    + intros. omicron; eauto using no_cr.
      eapply_tstep okcrs_preservation_spawned; eauto.
    + intros tid'' ?. omicron; eauto using no_cr.
      * eauto using nocr_preservation_spawn.
      * eapply_tstep okcrs_preservation_spawned; eauto.
Qed.

Theorem ucr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_crs ->
  forall_threads ths1 (valid_references m1) ->
  forall_threads ths1 ok_crs ->
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

