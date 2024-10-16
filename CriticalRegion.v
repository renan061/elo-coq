From Coq Require Import Lia.

From Elo Require Import Core.

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
  | okcrs_acq1   : forall t1 t2,  ~ value t1 ->
                                  ok_crs  t1 ->
                                  no_crs  t2 ->
                                  ok_crs <{acq t1 t2 }>
  | okcrs_acq2   : forall t1 t2,  value   t1 ->
                                  ~ value t2 ->
                                  no_crs  t1 ->
                                  ok_crs  t2 ->
                                  ok_crs <{acq t1 t2 }>
  | okcrs_acq3  : forall t1 t2,   value   t1 ->
                                  value   t2 ->
                                  no_crs  t1 ->
                                  no_crs  t2 ->
                                  ok_crs <{acq t1 t2 }>
  | okcrs_cr : forall ad t,       ok_crs t   ->
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
  ok_crs t.
Proof.
  intros. ind_tstep; invc_okcrs; eauto using nocrs_then_okcrs.
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
  eauto using okcrs_preservation_spawned. 
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
  tid < #ths ->
  unique_critical_regions m ths ->
  ths[tid] --[e_alloc (#m) te Te]--> t ->
  unique_critical_regions (m +++ (te, Te, false)) ths[tid <- t].
Proof.
  intros * ? [Hucr1 Hucr2] ?. split.
  - intros ? ? ?. omicron.
Abort.

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

Theorem ucr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 no_crs ->
  forall_threads ths1 ok_crs ->
  (* --- *)
  unique_critical_regions m1 ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  unique_critical_regions m2 ths2.
Proof.
  intros. invc_cstep; try invc_mstep;
  eauto using ucr_preservation_none; 
  eauto using ucr_preservation_read; 
  eauto using ucr_preservation_acq; 
  eauto using ucr_preservation_rel. 
  - admit.
  - admit.
  - admit.
Qed.


(*
(* inversion -- unique-crs ------------------------------------------------- *)

Local Ltac solve_inv_ucr1 :=
  intros * H ad'; specialize (H ad') as [? ?]; split; intros ?;
  auto_specialize; try solve [invc_nocr; assumption];
  match goal with Hor : _ \/ _ |- _ => destruct Hor end;
  (invc_nocr || invc_onecr); eauto.

Local Ltac solve_inv_ucr2 :=
  intros * ? H; invc_okcrs;
  split; intros ad'; specialize (H ad') as [? Hor]; split;
  intros ?; auto_specialize; try solve [invc_nocr; assumption];
  match goal with Hor : _ \/ _ |- _ => destruct Hor end;
  (invc_nocr || invc_onecr); eauto.

Local Lemma inv_ucrs_fun : forall m x Tx t,
  unique_crs m <{fn x Tx t}> ->
  unique_crs m t.
Proof. solve_inv_ucr1. Qed.

Local Lemma inv_ucrs_call : forall m t1 t2,
  ok_crs <{call t1 t2}> ->
  unique_crs m <{call t1 t2}> ->
  unique_crs m t1 /\ unique_crs m t2.
Proof. solve_inv_ucr2. Qed.

Local Lemma inv_ucrs_new : forall m t T,
  unique_crs m <{new t : T}> ->
  unique_crs m t.
Proof. solve_inv_ucr1. Qed.

Local Lemma inv_ucrs_load : forall m t,
  unique_crs m <{*t}> ->
  unique_crs m t.
Proof. solve_inv_ucr1. Qed.

Local Lemma inv_ucrs_asg : forall m t1 t2,
  ok_crs <{call t1 t2}> ->
  unique_crs m <{t1 := t2}> ->
  unique_crs m t1 /\ unique_crs m t2.
Proof. solve_inv_ucr2. Qed.

Local Lemma inv_ucrs_acq : forall m t1 t2,
  ok_crs <{call t1 t2}> ->
  unique_crs m <{acq t1 t2}> ->
  unique_crs m t1 /\ unique_crs m t2.
Proof. solve_inv_ucr2. Qed.

Local Lemma inv_ucrs_cr : forall m ad t,
  unique_crs m <{cr ad t}> ->
  unique_crs m t.
Proof. solve_inv_ucr1. Qed.

Local Lemma inv_ucrs_spawn : forall m t,
  unique_crs m <{spawn t}> ->
  unique_crs m t.
Proof. solve_inv_ucr1. Qed.

Ltac inv_ucrs :=
  match goal with
  | H : unique_crs _ <{unit     }> |- _ => idtac H
  | H : unique_crs _ <{nat _    }> |- _ => idtac H
  | H : unique_crs _ <{var _    }> |- _ => idtac H
  | H : unique_crs _ <{fn _ _ _ }> |- _ => eapply inv_ucrs_fun   in H as ?
  | H : unique_crs _ <{call _ _ }> |- _ => eapply inv_ucrs_call  in H as [? ?]
  | H : unique_crs _ <{& _ : _  }> |- _ => idtac H
  | H : unique_crs _ <{new _ : _}> |- _ => eapply inv_ucrs_new   in H as ?
  | H : unique_crs _ <{* _      }> |- _ => eapply inv_ucrs_load  in H as ?
  | H : unique_crs _ <{_ := _   }> |- _ => eapply inv_ucrs_asg   in H as [? ?]
  | H : unique_crs _ <{acq _ _  }> |- _ => eapply inv_ucrs_acq   in H as [? ?]
  | H : unique_crs _ <{cr _ _   }> |- _ => eapply inv_ucrs_cr    in H as ?
  | H : unique_crs _ <{spawn _  }> |- _ => eapply inv_ucrs_spawn in H as ?
  end.

Ltac invc_ucrs :=
  match goal with
  | H : unique_crs _ <{unit     }> |- _ => idtac H
  | H : unique_crs _ <{nat _    }> |- _ => idtac H
  | H : unique_crs _ <{var _    }> |- _ => idtac H
  | H : unique_crs _ <{fn _ _ _ }> |- _ => eapply inv_ucrs_fun   in H
  | H : unique_crs _ <{call _ _ }> |- _ => eapply inv_ucrs_call  in H as [? ?]
  | H : unique_crs _ <{& _ : _  }> |- _ => idtac H
  | H : unique_crs _ <{new _ : _}> |- _ => eapply inv_ucrs_new   in H
  | H : unique_crs _ <{* _      }> |- _ => eapply inv_ucrs_load  in H
  | H : unique_crs _ <{_ := _   }> |- _ => eapply inv_ucrs_asg   in H as [? ?]
  | H : unique_crs _ <{acq _ _  }> |- _ => eapply inv_ucrs_acq   in H as [? ?]
  | H : unique_crs _ <{cr _ _   }> |- _ => eapply inv_ucrs_cr    in H
  | H : unique_crs _ <{spawn _  }> |- _ => eapply inv_ucrs_spawn in H
  end.
*)

(* preservation -- unique-crs ---------------------------------------------- *)


Local Corollary ucrs_subst : forall m x tx t,
  no_crs t ->
  no_crs tx ->
  (* --- *)
  unique_crs m t ->
  unique_crs m tx ->
  unique_crs m <{[x := tx] t}>.
Proof.
  intros * ? ? Ht Htx ad.
  specialize (Ht ad) as [? Hort]. specialize (Htx ad) as [? Hortx].
  destruct (bool_eq_dec m[ad].X false) as [? | Hneq].
  - repeat auto_specialize. eauto using nocr_subst.
  - eapply Bool.not_false_is_true in Hneq. repeat auto_specialize.
    destruct Hort, Hortx; eauto using nocr_subst.
Qed.

(*
Local Lemma me_mem_add : forall m t te Te,
  unlocked_nocr m t ->
  unlocked_nocr (m +++ (te, Te, false)) t.
Proof.
  intros ** ? ?. omicron;
  match goal with |- no_cr ?ad _ =>
    specialize (H ad); sigma; eauto
  end.
Qed.

Local Lemma me_mem_set : forall m t ad te Te,
  unlocked_nocr m t ->
  unlocked_nocr m[ad.tT <- te Te] t.
Proof.
  intros ** ad' ?. omicron; eauto.
  decompose sum (lt_eq_lt_dec ad' (#m)); subst; eauto;
  match goal with |- no_cr ?ad _ =>
    specialize (H ad); sigma; eauto
  end.
Qed.

Local Ltac solve_me_preservation Hme ad :=
  ind_tstep; inv_me;
  try solve [invc_me; eauto using me_subst];
  intros ad'' ?; repeat auto_specialize; eauto using no_cr;
  destruct (nat_eq_dec ad'' ad); subst; eauto using no_cr;
  specialize (Hme ad); auto_specialize; invc_nocr; eauto.

Local Lemma me_preservation_none : forall m t1 t2,
  unlocked_nocr m t1 ->
  t1 --[e_none]--> t2 ->
  unlocked_nocr m t2.
Proof.
  intros * Hme ?. solve_me_preservation Hme ad.
Qed.

Local Lemma me_preservation_alloc : forall m t1 t2 ad t T,
  unlocked_nocr m t1 ->
  t1 --[e_alloc ad t T]--> t2 ->
  unlocked_nocr (m +++ (t, T, false)) t2.
Proof.
  intros * Hme ?. rename ad into ad'. eapply me_mem_add.
  solve_me_preservation Hme ad.
Qed.

Local Lemma me_preservation_read : forall m t1 t2 ad t,
  no_crs t ->
  (* --- *)
  unlocked_nocr m t1 ->
  t1 --[e_read ad t]--> t2 ->
  unlocked_nocr m t2.
Proof.
  intros * ? Hme ?. rename ad into ad'. solve_me_preservation Hme ad.
Qed.

Local Lemma me_preservation_write : forall m t1 t2 ad t T,
  unlocked_nocr m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  unlocked_nocr m[ad.tT <- t T]  t2.
Proof.
  intros * Hme ?. rename ad into ad'. eapply me_mem_set.
  solve_me_preservation Hme ad.
Qed.
*)

Local Lemma ucrs_preservation_acq : forall m t1 t2 ad t,
  no_crs t ->
  ok_crs t1 ->
  (* --- *)
  ad < #m ->
  m[ad].X = false ->
  unique_crs m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  unique_crs m[ad.X <- true] t2.
Proof. 
  intros * ? ? ? Hucrs **. rename ad into ad'.
  ind_tstep; inv_ucrs; invc_okcrs;
  repeat auto_specialize; repeat clean; eauto using ok_crs;
  try solve [exfalso; eauto using value_does_not_step, value];
  try solve [intros ad''; split; intros ?; omicron;
    specialize (IHtstep ad'') as [? Hor]; sigma; eauto using no_cr;
    auto_specialize; destruct Hor; eauto using no_cr, one_cr].
  - repeat invc_ucrs. repeat invc_nocrs.
    intros ?. omicron; eauto.
    + split; intros ?; try discriminate.
      eauto using nocrs_then_nocr, nocrs_subst, one_cr.
    + split; eauto using nocrs_then_nocr, nocrs_subst, no_cr.
  - destruct (H2 ad) as [? Hor]. destruct (m[ad].X).
    + auto_specialize. destruct Hor.
      * invc_nocr.
      * invc_onecr; eauto. intros ad''. split; intros ?.
        ** omicron. destruct (nat_eq_dec ad'' ad); subst.
           *** specialize (H2 ad) as [? _]. auto_specialize. invc_nocr.
           *** eapply nocr_cr; eauto.
               specialize (IHtstep ad'') as [? _]. sigma. eauto.
        ** omicron; destruct (nat_eq_dec ad'' ad); subst.
           *** specialize (H2 ad) as [? _]. auto_specialize.
               invc_nocr.
           *** specialize (IHtstep ad'') as [_ ?]. sigma.
               auto_specialize. destruct H6; eauto using no_cr, one_cr.
           *** destruct (H2 ad) as [_ ?]. auto_specialize.
               specialize (IHtstep ad) as [_ ?]. sigma. auto_specialize.
               destruct H6; try solve [invc_nocr; eauto].
               invc_onecr.
               **** right. eapply onecr_cr_eq.
                    eauto using nocr_preservation_acq_neq.
               **** specialize (H2 ad) as [_ ?]. auto_specialize.
                    destruct H2; try solve [invc_nocr; eauto].
                    invc_onecr; eauto.
           *** specialize (IHtstep ad'') as [_ ?]. sigma. 
               auto_specialize.
               destruct H6; eauto using no_cr, one_cr.
    + clear Hor. auto_specialize. invc_nocr.
Qed.

Local Lemma blop : forall m t ad,
  unique_crs m <{cr ad t}> ->
  m[ad].X = true.
Proof.
  intros * H. specialize (H ad) as [? Hor].
  destruct (m[ad].X); aspecialize; trivial. invc_nocr.
Qed.

Local Lemma ucrs_preservation_rel : forall m t1 t2 ad,
  ok_crs t1 ->
  (* --- *)
  ad < #m ->
  unique_crs m t1 ->
  t1 --[e_rel ad]--> t2 ->
  unique_crs m[ad.X <- false] t2.
Proof. 
  intros * ? ? Hucrs ?. rename ad into ad'.
  ind_tstep; invc_okcrs; inv_ucrs; clean; repeat aspecialize;
  eauto using ok_crs;
  try solve [exfalso; eauto using value_does_not_step];
  try solve [
    intros ad''; specialize (IHtstep ad'') as [? Hor]; split; intros ?;
    omicron; aspecialize; eauto using no_cr;
    destruct Hor; eauto using no_cr, one_cr
  ].
  - intros ad''. specialize (IHtstep ad'') as [? Hor1]. split; intros ?.
    + specialize (Hucrs ad) as [? Hor2]. destruct (nat_eq_dec ad'' ad); subst.
      * omicron; aspecialize; repeat clean.
        ** destruct (m[ad].X); repeat aspecialize.
           *** destruct Hor2; try solve [invc_nocr]. invc_onecr; eauto.
               exfalso. eauto using nocr_preservation_rel_eq.
           *** invc_nocr.
        ** destruct (m[ad].X); repeat aspecialize.
           *** invc_nocr.
           *** invc_nocr.
      * omicron; aspecialize; repeat clean; eauto using no_cr.
    + specialize (Hucrs ad) as [? Hor2]. destruct (nat_eq_dec ad'' ad); subst.
      * omicron; aspecialize; repeat clean.
        destruct (m[ad].X); repeat aspecialize; try solve [invc_nocr].
        destruct Hor2; try solve [invc_nocr]. invc_onecr; eauto.
        eauto using nocr_preservation_rel_neq, one_cr.
      * omicron; aspecialize; repeat clean.
        destruct (m[ad].X); repeat aspecialize; try solve [invc_nocr].
        destruct Hor2; try solve [invc_nocr]. invc_onecr; eauto.
        destruct Hor1; eauto using nocr_preservation_rel_neq, no_cr, one_cr.
  - eapply blop in Hucrs. intros ?. split.
    + omicron; intros ?; eauto using nocrs_then_nocr, value_then_nocrs.
    + omicron; intros ?; eauto using nocrs_then_nocr, value_then_nocrs.
Qed.

Local Lemma me_preservation_rel : forall m t1 t2 ad,
  ad < #m ->
  unlocked_nocr m t1 ->
  t1 --[e_rel ad]--> t2 ->
  unlocked_nocr m[ad.X <- false] t2.
Proof. 
  intros * ? Hme **. rename ad into ad'; ind_tstep; inv_me; intros ad'' ?.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - repeat clean. repeat auto_specialize. omicron.
    + destruct (nat_eq_dec ad'' ad); subst.
      * specialize (IHtstep ad). sigma. auto_specialize.
        destruct (bool_eq_dec (m[ad].X) false) as [Heq | Hneq].
        ** specialize (Hme ad). auto_specialize. invc_nocr. eauto.
        ** exfalso.
           eapply Bool.not_false_is_true in Hneq.
           assert (H' : locked_onecr m <{cr ad t}>) by admit.
           specialize (H' ad Hneq). invc H'; eauto using nocr_preservation_rel.
      * specialize (IHtstep ad''). sigma. eauto using no_cr.
    + specialize (IHtstep ad''). sigma. eapply nocr_cr; eauto. intros ?; subst.
      specialize (Hme ad). repeat auto_specialize. invc_nocr. eauto.
  - repeat clean. omicron.
    + admit. (* Usando ok_cr simples. => value has no cr *)
    + admit. (* Usando ok_cr simples. => value has no cr *)







  try solve [specialize (IHtstep ad''); sigma; eauto using no_cr].
  destruct (nat_eq_dec ad'' ad); subst.
  intros * ? Hme **. rename ad into ad';
  ind_tstep; inv_me; intros ad'' ?; omicron; repeat auto_specialize; eauto;
  try solve [specialize (IHtstep ad''); sigma; eauto using no_cr].
  destruct (nat_eq_dec ad'' ad); subst.
  - specialize (Hme ad). auto_specialize. invc_nocr. eauto.
  - specialize (IHtstep ad''). sigma. eauto using no_cr.
Qed.

Local Lemma me_preservation_spawn : forall m t1 t2 tid t,
  unlocked_nocr m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  unlocked_nocr m t2.
Proof.
  intros * Hme ?. solve_me_preservation Hme ad.
Qed.

Local Corollary me_preservation_mstep : forall m1 m2 t1 t2 e,
  forall_memory m1 no_crs ->
  (* --- *)
  unlocked_nocr m1 t1 ->
  m1 / t1 ==[e]==> m2 / t2 ->
  unlocked_nocr m2 t2.
Proof.
  intros. invc_mstep;
  eauto using me_preservation_none,
              me_preservation_alloc,
              me_preservation_read,
              me_preservation_write,
              me_preservation_acq,
              me_preservation_rel.
Qed.























(* ------------------------------------------------------------------------- *)
(* in-cr                                                                     *)
(* ------------------------------------------------------------------------- *)

(* Ignores spawn blocks. *)
Inductive in_cr (ad : addr) : tm -> Prop :=
  | incr_fun   : forall x Tx t, in_cr ad t   -> in_cr ad <{fn x Tx t }>
  | incr_call1 : forall t1 t2,  in_cr ad t1  -> in_cr ad <{call t1 t2}>
  | incr_call2 : forall t1 t2,  in_cr ad t2  -> in_cr ad <{call t1 t2}>
  | incr_new   : forall T t,    in_cr ad t   -> in_cr ad <{new t : T }>
  | incr_load  : forall t,      in_cr ad t   -> in_cr ad <{*t        }>
  | incr_asg1  : forall t1 t2,  in_cr ad t1  -> in_cr ad <{t1 := t2  }>
  | incr_asg2  : forall t1 t2,  in_cr ad t2  -> in_cr ad <{t1 := t2  }>
  | incr_acq1  : forall t1 t2,  in_cr ad t1  -> in_cr ad <{acq t1 t2 }>
  | incr_acq2  : forall t1 t2,  in_cr ad t2  -> in_cr ad <{acq t1 t2 }>
  | incr_cr1   : forall t,                      in_cr ad <{cr ad  t  }>
  | incr_cr2   : forall ad' t,  in_cr ad t   -> in_cr ad <{cr ad' t  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _incr tt :=
  match goal with
  | H : in_cr _ <{unit     }> |- _ => tt H
  | H : in_cr _ <{nat _    }> |- _ => tt H
  | H : in_cr _ <{var _    }> |- _ => tt H
  | H : in_cr _ <{fn _ _ _ }> |- _ => tt H
  | H : in_cr _ <{call _ _ }> |- _ => tt H
  | H : in_cr _ <{& _ : _  }> |- _ => tt H
  | H : in_cr _ <{new _ : _}> |- _ => tt H
  | H : in_cr _ <{* _      }> |- _ => tt H
  | H : in_cr _ <{_ := _   }> |- _ => tt H
  | H : in_cr _ <{acq _ _  }> |- _ => tt H
  | H : in_cr _ <{cr _ _   }> |- _ => tt H
  | H : in_cr _ <{spawn _  }> |- _ => tt H
  end.

Ltac inv_incr  := _incr inv.
Ltac invc_incr := _incr invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma nocrs_then_nincr : forall ad t,
  no_crs t ->
  ~ in_cr ad t.
Proof.
  intros ** ?. induction t; invc_nocrs; invc_incr; eauto.
Qed.

Lemma nincr_spawned : forall ad t t1 t2 tid,
  ok_crs t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  ~ in_cr ad t.
Proof.
  intros. ind_tstep; invc_okcrs;
  eauto using nocrs_then_okcrs, nocrs_then_nincr.
Qed.

(* inheritance ------------------------------------------------------------- *)

Local Lemma incr_inheritance_subst : forall ad x Tx t tx,
  in_cr ad <{[x := tx] t}> ->
  in_cr ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; eauto; simpl in *;
  try (destruct str_eq_dec; subst; eauto using in_cr);
  invc_incr; repeat auto_specialize; repeat invc_incr; eauto using in_cr.
Qed.

Local Lemma incr_inheritance_none : forall t1 t2 ad,
  in_cr ad t2 ->
  t1 --[e_none]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using incr_inheritance_subst, in_cr.
Qed.

Local Lemma incr_inheritance_alloc : forall t1 t2 ad ad' t T,
  in_cr ad t2 ->
  t1 --[e_alloc ad' t T]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using in_cr.
Qed.

Local Lemma incr_inheritance_read : forall t1 t2 ad ad' t,
  value t ->
  ok_crs t ->
  (* --- *)
  in_cr ad t2 ->
  t1 --[e_read ad' t]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using in_cr.
  exfalso. eapply nocrs_then_nincr; eauto using value_then_nocrs.
Qed.

Local Lemma incr_inheritance_write : forall t1 t2 ad ad' t T,
  in_cr ad t2 ->
  t1 --[e_write ad' t T]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using in_cr.
Qed.

Local Lemma incr_inheritance_acq : forall t1 t2 ad ad' t,
  value t ->
  ok_crs t ->
  ok_crs t1 ->
  (* --- *)
  ad <> ad' ->
  in_cr ad t2 ->
  t1 --[e_acq ad' t]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; repeat invc_okcrs; try invc_incr;
  eauto using nocrs_then_okcrs, in_cr;
  exfalso; eauto using value.
  invc_nocrs.
  eapply nocrs_then_nincr. 2: eauto. eauto using value_then_nocrs, nocrs_subst.
Qed.

Local Lemma incr_inheritance_rel : forall t1 t2 ad ad',
  ok_crs t1 ->
  (* --- *)
  in_cr ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; invc_okcrs; try invc_incr;
  eauto using nocrs_then_okcrs, in_cr.
Qed.

Local Lemma incr_inheritance_spawn : forall t1 t2 ad tid t,
  in_cr ad t2 ->
  t1 --[e_spawn tid t]--> t2 ->
  in_cr ad t1.
Proof.
  intros. ind_tstep; try invc_incr; eauto using in_cr.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Lemma incr_subst : forall t tx ad x,
  in_cr ad t ->
  in_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; eauto; simpl in *;
  try (destruct str_eq_dec; subst); invc_incr; eauto using in_cr.
Qed.

Local Lemma incr_preservation_none : forall t1 t2 ad,
  ok_crs t1 ->
  (* --- *)
  in_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  in_cr ad t2.
Proof.
  intros. ind_tstep; repeat invc_okcrs; repeat invc_incr;
  eauto using nocrs_then_okcrs, incr_subst, in_cr.
  - exfalso. eauto using value.
  - match goal with H : in_cr _ _ |- _ => contradict H end.
    eauto using value_then_nocrs, nocrs_then_nincr.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-in-cr                                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_inv_nincr := intros; try split; eauto using in_cr.

Local Lemma inv_nincr_fun : forall ad x Tx t,
  ~ in_cr ad <{fn x Tx t}> -> ~ in_cr ad t.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_call : forall ad t1 t2,
  ~ in_cr ad <{call t1 t2}> -> ~ in_cr ad t1 /\ ~ in_cr ad t2.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_new : forall ad t T,
  ~ in_cr ad <{new t : T}> -> ~ in_cr ad t.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_load : forall ad t,
  ~ in_cr ad <{*t}> -> ~ in_cr ad t.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_asg : forall ad t1 t2,
  ~ in_cr ad <{t1 := t2}> -> ~ in_cr ad t1 /\ ~ in_cr ad t2.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_acq : forall ad t1 t2,
  ~ in_cr ad <{acq t1 t2}> -> ~ in_cr ad t1 /\ ~ in_cr ad t2.
Proof. solve_inv_nincr. Qed.

Local Lemma inv_nincr_neq : forall ad ad' t,
  ~ in_cr ad <{cr ad' t}> -> ad <> ad' /\ ~ in_cr ad t.
Proof.
  intros * H. split. intros ?.
  - subst. eauto using in_cr.
  - intros ?. destruct (nat_eq_dec ad ad'); subst; eauto using in_cr.
Qed.

Ltac invc_nincr :=
  match goal with
  | H : ~ in_cr _   <{unit     }> |- _ => clear H
  | H : ~ in_cr _   <{nat _    }> |- _ => clear H
  | H : ~ in_cr _   <{var _    }> |- _ => clear H
  | H : ~ in_cr _   <{fn _ _ _ }> |- _ => eapply inv_nincr_fun    in H
  | H : ~ in_cr _   <{call _ _ }> |- _ => eapply inv_nincr_call   in H as [? ?]
  | H : ~ in_cr _   <{& _ : _  }> |- _ => clear H
  | H : ~ in_cr _   <{new _ : _}> |- _ => eapply inv_nincr_new    in H
  | H : ~ in_cr _   <{* _      }> |- _ => eapply inv_nincr_load   in H
  | H : ~ in_cr _   <{_ := _   }> |- _ => eapply inv_nincr_asg    in H as [? ?]
  | H : ~ in_cr _   <{acq _ _  }> |- _ => eapply inv_nincr_acq    in H as [? ?]
  | H : ~ in_cr ?ad <{cr ?ad _ }> |- _ => contradict H; eauto using in_cr
  | H : ~ in_cr _   <{cr _ _   }> |- _ => eapply inv_nincr_neq    in H as [? ?]
  | H : ~ in_cr _   <{spawn _  }> |- _ => clear H
  end.

(* preservation ------------------------------------------------------------ *)

Local Lemma nincr_subst : forall ad x tx t,
  no_crs t ->
  (* --- *)
  ~ in_cr ad t ->
  ~ in_cr ad tx ->
  ~ in_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_nocrs; trivial; simpl in *;
  try (destruct str_eq_dec; subst); eauto using in_cr;
  invc_nincr; repeat auto_specialize; intros ?; invc_incr; eauto.
Qed.

Local Ltac solve_nincr_preservation :=
  intros; ind_tstep; repeat invc_okcrs; repeat invc_nincr; repeat invc_nocrs;
  eauto using nincr_subst, value_then_nocrs, nocrs_then_nincr;
  solve [ exfalso; eauto using value_does_not_step
        | repeat auto_specialize; intros ?; invc_incr; eauto
        ].

Local Lemma nincr_preservation_none : forall t1 t2 ad,
  ok_crs t1 ->
  (* --- *)
  ~ in_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation. Qed.

Local Lemma nincr_preservation_alloc : forall t1 t2 ad ad' t T,
  ~ in_cr ad t1 ->
  t1 --[e_alloc ad' t T]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation. Qed.

Local Lemma nincr_preservation_read : forall t1 t2 ad ad' t,
  value t ->
  ok_crs t ->
  (* --- *)
  ~ in_cr ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation. Qed.

Local Lemma nincr_preservation_write : forall t1 t2 ad ad' t T,
  ~ in_cr ad t1 ->
  t1 --[e_write ad' t T]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation. Qed.

Local Lemma nincr_preservation_acq : forall t1 t2 ad ad' t,
  value t ->
  ok_crs t ->
  ok_crs t1 ->
  (* --- *)
  ad <> ad' ->
  ~ in_cr ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  ~ in_cr ad t2.
Proof.
  intros; ind_tstep; repeat invc_okcrs; repeat invc_nincr;
  try solve [ exfalso; eauto using value_does_not_step, value
            |  intros ?; invc_incr; eauto; repeat auto_specialize; eauto
            ].
  invc_nocrs. intros ?. invc_incr; eauto. eapply nincr_subst. 4: eauto.
  - assumption.
  - assumption.
  - eauto using value_then_nocrs, nocrs_then_nincr.
Qed.

Local Lemma nincr_preservation_rel : forall t1 t2 ad ad',
  ~ in_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation. Qed.

Local Lemma nincr_preservation_spawn : forall t1 t2 ad tid t,
  ~ in_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  ~ in_cr ad t2.
Proof. solve_nincr_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* lock-exclusivity                                                          *)
(* ------------------------------------------------------------------------- *)

Definition locked_cr (m : mem) (t : tm) := forall ad,
  in_cr ad t ->
  m[ad].X = true.

Theorem lcr_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_memory m1 ok_crs ->
  forall_threads ths1 ok_crs ->
  (* --- *)
  forall_threads ths1 (locked_cr m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (locked_cr m2).
Proof.
  unfold locked_cr.
  intros ** tid' **. invc_cstep; try invc_mstep.
  - omicron; eauto using incr_inheritance_none.
  - repeat omicron; eauto using incr_inheritance_alloc.
    + specialize (H2 tid' (#m1)). sigma. eauto using incr_inheritance_alloc. 
    + specialize (H2 tid' ad).    sigma. eauto using incr_inheritance_alloc. 
    + specialize (H2 tid' (#m1)). sigma. eauto.
    + specialize (H2 tid' ad).    sigma. eauto.
  - omicron; eauto using incr_inheritance_read.
  - repeat omicron; eauto using incr_inheritance_write.
  - repeat omicron; eauto using incr_inheritance_acq. 
  - repeat omicron; eauto.
    + specialize (H2 tid' ad).
      (* contradict H4 *)
      admit.
    + eauto using incr_inheritance_rel. 
    + specialize (H2 tid' ad H4).
      (* Se deu o passo, então *)
      admit.
  - omicron; eauto using incr_inheritance_spawn.
    + contradict H4. eauto using nincr_spawned.
    + invc_incr.
Abort.

(* ------------------------------------------------------------------------- *)
(* critical-region-exclusivity                                               *)
(* ------------------------------------------------------------------------- *)

Definition critical_region_exclusivity (ths : threads) := forall ad tid1 tid2,
  tid1 <> tid2 ->
  in_cr ad ths[tid1] ->
  ~ in_cr ad ths[tid2].

(* preservation ------------------------------------------------------------ *)

Local Lemma tstep_length_tid : forall ths tid e t,
  ths[tid] --[e]--> t ->
  tid < #ths.
Proof.
  intros.
  decompose sum (lt_eq_lt_dec tid (#ths)); subst; sigma; eauto; invc_tstep.
Qed.

Local Ltac destruct_cre ths tid tid1 tid2 :=
  assert (Hlt : tid < #ths) by eauto using tstep_length_tid;
  destruct (nat_eq_dec tid tid1), (nat_eq_dec tid tid2); subst;
  try contradiction.

Local Lemma cre_preservation_none : forall t ths tid,
  ok_crs ths[tid] ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_none]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_none, nincr_preservation_none.
Qed.

Local Lemma cre_preservation_alloc : forall t ths tid ad te T,
  critical_region_exclusivity ths ->
  ths[tid] --[e_alloc ad te T]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_alloc, nincr_preservation_alloc.
Qed.

Local Lemma cre_preservation_read : forall t ths tid ad te,
  value te ->
  ok_crs te ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_read ad te]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_read, nincr_preservation_read.
Qed.

Local Lemma cre_preservation_write : forall t ths tid ad te T,
  critical_region_exclusivity ths ->
  ths[tid] --[e_write ad te T]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_write, nincr_preservation_write.
Qed.

Local Lemma cre_preservation_rel : forall t ths tid ad,
  forall_threads ths ok_crs ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_rel ad]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; sigma;
  eauto using incr_inheritance_rel, nincr_preservation_rel.
Qed.

Local Lemma cre_preservation_acq : forall m t ths tid ad te,
  m[ad].X = false ->
  value te ->
  ok_crs te ->
  forall_threads ths ok_crs ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_acq ad te]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros * ? ? ? ? ? ? ad' **.
  destruct_cre ths tid tid1 tid2; sigma; eauto;
  destruct (nat_eq_dec ad' ad); subst;
  eauto using nincr_preservation_acq, incr_inheritance_acq.
  - (*
      - tid1 steps
      - t has CR(ad) after the acq
      - we want to show tid2 does not have it
    *)
    admit.
  - (*
      - tid2 steps
      - tid1 has CR(ad)
      - we want to show t does not have it (after the step)
    *)
    admit.
Abort.

Local Lemma cre_preservation_spawn : forall t ths tid tid' te,
  forall_threads ths ok_crs ->
  (* --- *)
  critical_region_exclusivity ths ->
  ths[tid] --[e_spawn tid' te]--> t ->
  critical_region_exclusivity (ths[tid <- t] +++ te).
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2; repeat omicron;
  eauto; try solve [lia | intros ?; invc_incr];
  eauto using incr_inheritance_spawn, nincr_preservation_spawn, nincr_spawned;
  match goal with
  | H : in_cr _ _ |- _ => contradict H; eauto using nincr_spawned
  end.
Qed.

Theorem cre_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  forall_program m1 ths1 ok_crs ->
  (* --- *)
  critical_region_exclusivity ths1 ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  critical_region_exclusivity ths2.
Proof.
  intros * ? [? ?] **. invc_cstep; try invc_mstep;
  eauto using cre_preservation_none,
              cre_preservation_alloc,
              cre_preservation_read,
              cre_preservation_write,
              cre_preservation_rel,
              cre_preservation_spawn.

  intros ad' tid1 tid2 Hneq Hincr.
  omicron; eauto.
  -

  specialize (H2 tid ad). auto_specialize.
Qed.
