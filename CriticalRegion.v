From Elo Require Import Core.

From Elo Require Import WellTypedTerm.

(* ------------------------------------------------------------------------- *)
(* insideCR                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Ignores spawn blocks. *)
Inductive insideCR (ad : addr) : tm -> Prop :=
  | icr_fun : forall x Tx t,
    insideCR ad t ->
    insideCR ad <{fn x Tx t}>

  | icr_call1 : forall t1 t2,
    insideCR ad t1 ->
    insideCR ad <{call t1 t2}>

  | icr_call2 : forall t1 t2,
    insideCR ad t2 ->
    insideCR ad <{call t1 t2}>

  | icr_new : forall T t,
    insideCR ad t ->
    insideCR ad <{new t : T}>

  | icr_load : forall t,
    insideCR ad t ->
    insideCR ad <{*t}>

  | icr_asg1 : forall t1 t2,
    insideCR ad t1 ->
    insideCR ad <{t1 := t2}>

  | icr_asg2 : forall t1 t2,
    insideCR ad t2 ->
    insideCR ad <{t1 := t2}>

  | icr_acq1 : forall t1 t2,
    insideCR ad t1 ->
    insideCR ad <{acq t1 t2}>

  | icr_acq2 : forall t1 t2,
    insideCR ad t2 ->
    insideCR ad <{acq t1 t2}>

  | icr_cr_eq : forall t,
    insideCR ad <{cr ad t}>

  | icr_cr_neq : forall ad' t,
    ad <> ad' ->
    insideCR ad t ->
    insideCR ad <{cr ad' t}>
  .

(* ------------------------------------------------------------------------- *)
(* tactics                                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac _icr tt :=
  match goal with
  | H : insideCR _ <{unit     }> |- _ => tt H
  | H : insideCR _ <{nat _    }> |- _ => tt H
  | H : insideCR _ <{var _    }> |- _ => tt H
  | H : insideCR _ <{fn _ _ _ }> |- _ => tt H
  | H : insideCR _ <{call _ _ }> |- _ => tt H
  | H : insideCR _ <{& _ : _  }> |- _ => tt H
  | H : insideCR _ <{new _ : _}> |- _ => tt H
  | H : insideCR _ <{* _      }> |- _ => tt H
  | H : insideCR _ <{_ := _   }> |- _ => tt H
  | H : insideCR _ <{acq _ _  }> |- _ => tt H
  | H : insideCR _ <{cr _ _   }> |- _ => tt H
  | H : insideCR _ <{spawn _  }> |- _ => tt H
  end.

Ltac inv_icr  := _icr inv.
Ltac invc_icr := _icr invc.

Local Ltac _value tt :=
  match goal with
  (* irrelevant for unit and nat *)
  | H : value <{var _    }> |- _ => tt H
  (* irrelevant for function *)
  | H : value <{call _ _ }> |- _ => tt H
  (* irrelevant for reference *)
  | H : value <{new _ : _}> |- _ => tt H
  | H : value <{* _      }> |- _ => tt H
  | H : value <{_ := _   }> |- _ => tt H
  | H : value <{acq _ _  }> |- _ => tt H
  | H : value <{cr _ _   }> |- _ => tt H
  | H : value <{spawn _  }> |- _ => tt H
  end.

Ltac inv_value  := _value inv.
Ltac invc_value := _value invc.

(* ------------------------------------------------------------------------- *)
(* value-icr                                                                 *)
(* ------------------------------------------------------------------------- *)

Definition value_icr t := forall ad, value t -> ~ insideCR ad t.

Local Lemma vicr_preservation_none : forall t1 t2,
  value_icr t1 ->
  t1 --[e_none]--> t2 ->
  value_icr t2.
Proof.
  unfold value_icr. intros * Hvicr **.
  ind_tstep.
  - invc_value.
  - invc_value.
  - admit.
  - invc_value.
  - invc_value.
  - invc_value.
  - invc_value.
  - invc_value.
  - invc_value.
  - admit.
Qed.


(* ------------------------------------------------------------------------- *)
(* insideCR inheritance                                                          *)
(* ------------------------------------------------------------------------- *)

Local Lemma icr_inheritance_subst : forall ad x Tx t tx,
  insideCR ad <{[x := tx] t}> ->
  insideCR ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. induction t; eauto; simpl in *;
  try (destruct str_eq_dec; subst; eauto using insideCR);
  invc_icr; repeat auto_specialize; repeat invc_icr; eauto using insideCR.
Qed.

Local Lemma icr_inheritance_none : forall t1 t2 ad,
  insideCR ad t2 ->
  t1 --[e_none]--> t2 ->
  insideCR ad t1.
Proof.
  intros. ind_tstep; try invc_icr; eauto using icr_inheritance_subst, insideCR.
Qed.

(* ------------------------------------------------------------------------- *)
(* insideCR preservation                                                         *)
(* ------------------------------------------------------------------------- *)

Local Lemma icr_subst : forall t tx ad x,
  insideCR ad t ->
  insideCR ad <{[x := tx] t}>.
Proof.
  intros. induction t; eauto; simpl in *;
  try (destruct str_eq_dec; subst); invc_icr; eauto using insideCR.
Qed.

Local Lemma icr_preservation_none : forall t1 t2 ad,
  well_typed_term t1 ->
  insideCR ad t1 ->
  t1 --[e_none]--> t2 ->
  insideCR ad t2.
Proof.
  intros. ind_tstep; invc_wtt; repeat invc_icr; eauto using insideCR.
  - eauto using icr_subst.
  - invc H0; invc_icr. admit.
Qed.


(* ------------------------------------------------------------------------- *)
(* invariant                                                                 *)
(* ------------------------------------------------------------------------- *)

Definition critical_region_exclusivity (ths : threads) := forall ad tid1 tid2,
  tid1 <> tid2 ->
  insideCR ad ths[tid1] ->
  ~ insideCR ad ths[tid2].

(* ------------------------------------------------------------------------- *)
(* preservation                                                              *)
(* ------------------------------------------------------------------------- *)

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
  critical_region_exclusivity ths ->
  ths[tid] --[e_none]--> t ->
  critical_region_exclusivity ths[tid <- t].
Proof.
  unfold critical_region_exclusivity. intros.
  destruct_cre ths tid tid1 tid2.
  - sigma. eauto using icr_inheritance_none.
  - sigma.

  ind_tstep; intros ? ? ? Hneq Hicr;
  repeat clean; repeat auto_specialize.
  - admit.
  - admit.
  - admit.
  - destruct (nat_eq_dec tid1 tid); destruct (nat_eq_dec tid2 tid); subst;
    sigma; eauto.
    + invc_icr. specialize (IHtstep ad tid tid2 Hneq). sigma. eauto.
    + specialize (IHtstep ad tid1 tid Hneq). sigma. intros ?. invc_icr.
      eapply IHtstep; eauto.




  - intros ? ? ? Hneq Hicr.
    repeat clean. repeat auto_specialize.
    destruct (nat_eq_dec tid1 tid); destruct (nat_eq_dec tid2 tid); subst;
    sigma; eauto.
    + admit.
    +


      invc_icr.
      * specialize (IHtstep ad tid2 tid1 Hneq). sigma.
        intros ?. eapply IHtstep; eauto.
      * eapply not_eq_sym in Hneq as Hneq1.
        specialize (IHtstep ad tid1 tid2 Hneq1) as IH1. sigma.
        eapply IH1. clear IH1.
        specialize (IHtstep ad tid2 tid1 Hneq) as IH2. sigma.

Qed.
