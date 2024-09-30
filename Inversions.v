From Coq Require Import Lia.

From Elo Require Import Core.
From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* unfold hints                                                              *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Unfold well_typed_term : wtt.
#[export] Hint Unfold safe_access     : sacc.

#[export] Hint Extern 4 => unfold well_typed_term : wtt.
#[export] Hint Extern 4 => unfold safe_access     : sacc.

(*

(* ------------------------------------------------------------------------- *)
(* inversions -- access & write-access                                       *)
(* ------------------------------------------------------------------------- *)

Local Ltac _accs P tt :=
  match goal with
  | H : P _ _ <{unit    }>   |- _ => tt H
  | H : P _ _ <{nat _   }>   |- _ => tt H
  | H : P _ _ <{var _   }>   |- _ => tt H
  | H : P _ _ <{fn _ _ _}>   |- _ => tt H
  | H : P _ _ <{call _ _}>   |- _ => tt H
  | H : P _ _ <{& _ :: _}>   |- _ => tt H
  | H : P _ _ <{new _ _ }>   |- _ => tt H
  | H : P _ _ <{* _     }>   |- _ => tt H
  | H : P _ _ <{_ = _   }>   |- _ => tt H
  | H : P _ _ <{acq _  _}>   |- _ => tt H
  | H : P _ _ <{cr _ _  }>   |- _ => tt H
  | H : P _ _ <{ptm _ _ }>   |- _ => tt H
  | H : P _ _ <{spawn _ }>   |- _ => tt H
  end.

Ltac inv_acc  := _accs access inv.
Ltac invc_acc := _accs access invc.

Ltac inv_wacc  := _accs write_access invc.
Ltac invc_wacc := _accs write_access invc.

(* ------------------------------------------------------------------------- *)
(* not-write-access inversion                                                *)
(* ------------------------------------------------------------------------- *)

Local Lemma inv_nwacc_ref_eq : forall m ad T,
  ~ unsafe_access ad m <{&ad :: &T}> ->
  False.
Proof. eauto using unsafe_access. Qed.

Local Lemma inv_nuacc_ref_neqM : forall m ad ad' T,
  ~ unsafe_access ad m <{&ad' :: &T}> ->
  (ad <> ad' /\ ~ unsafe_access ad m m[ad'].tm).
Proof.
  intros. destruct (nat_eq_dec ad ad'); subst; eauto using unsafe_access.
  exfalso. eauto using inv_nuacc_ref_eq.
Qed.

Lemma inv_nuacc_ref_neqI : forall m ad ad' T,
  forall_memory m value ->
  consistently_typed_references m <{&ad' :: i&T}> ->
  (* --- *)
  ~ unsafe_access ad m <{&ad' :: i&T}> ->
  ~ unsafe_access ad m m[ad'].tm.
Proof.
  intros * Hval **. invc_ctr. intros ?.
  specialize (Hval ad'); simpl in *.
  destruct Hval; inv_type; inv_uacc; eauto.
Qed.

Local Ltac solve_nuacc_inversion :=
  intros; try (split; intros); eauto using unsafe_access.

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
  | H : ~ unsafe_access ?ad _ <{& ?ad  :: & _ }> |- _ =>
    eapply inv_nuacc_ref_eq   in H; solve contradiction
  | H : ~ unsafe_access ?ad _ <{& ?ad' :: & _ }> |- _ =>
    eapply inv_nuacc_ref_neqM in H as [? ?]
  | H : ~ unsafe_access _ _   <{new _ _       }> |- _ =>

  | Hval   : forall_memory ?m value,
    Hctr   : consistently_typed_references ?m <{& ?ad' :: (i& ?T) }>,
    Hnuacc : ~ unsafe_access ?ad ?m <{& ?ad' :: (i& ?T) }> |- _ =>
    eapply (inv_nuacc_ref_neqI m ad ad' T Hval Hctr) in Hnuacc
  end.

(* ------------------------------------------------------------------------- *)
(* not-access inversion                                                      *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_nacc_inversion := 
  intros; try split; eauto using access.

Local Lemma inv_nacc_ref : forall m ad ad' T,
  ~ access ad m <{&ad' :: T}> ->
  ad <> ad' /\ ~ access ad m (m[ad'].tm).
Proof.
  intros. assert (ad <> ad') by (intros ?; subst; eauto using access).
  split; eauto using access.
Qed.

Local Lemma inv_nacc_new : forall m t ad T,
  ~ access ad m <{new T t}> ->
  ~ access ad m t.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_load : forall m t ad,
  ~ access ad m <{*t}> ->
  ~ access ad m t.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_asg : forall m t1 t2 ad,
  ~ access ad m <{t1 = t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_fun : forall m x Tx t ad,
  ~ access ad m <{fn x Tx t}> ->
  ~ access ad m t.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_call : forall m t1 t2 ad,
  ~ access ad m <{call t1 t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_nacc_inversion. Qed.

Local Lemma inv_nacc_seq : forall m t1 t2 ad,
  ~ access ad m <{t1; t2}> ->
  ~ access ad m t1 /\ ~ access ad m t2.
Proof. solve_nacc_inversion. Qed.

Ltac inv_nacc :=
  match goal with
  (* irrelevant for unit  *)
  (* irrelevant for num   *)
  | H : ~ access _ _ <{& _ :: _}> |- _ => eapply inv_nacc_ref   in H as [? ?]
  | H : ~ access _ _ <{new _ _ }> |- _ => eapply inv_nacc_new  in H
  | H : ~ access _ _ <{* _     }> |- _ => eapply inv_nacc_load in H
  | H : ~ access _ _ <{_ = _   }> |- _ => eapply inv_nacc_asg  in H as [? ?]
  (* irrelevant for var   *)                    
  | H : ~ access _ _ <{fn _ _ _}> |- _ => eapply inv_nacc_fun  in H
  | H : ~ access _ _ <{call _ _}> |- _ => eapply inv_nacc_call in H as [? ?]
  | H : ~ access _ _ <{_ ; _   }> |- _ => eapply inv_nacc_seq  in H as [? ?]
  (* irrelevant for spawn *)                    
  end.

(* ------------------------------------------------------------------------- *)
(* no-mut inversion                                                          *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_nomut tt :=
  match goal with
  (* irrelevant for unit      *)
  (* irrelevant for num       *)
  | H : no_mut <{& _ :: Unit     }> |- _ => tt H
  | H : no_mut <{& _ :: Num      }> |- _ => tt H
  (* irrelevant if &ad :: i&T *)
  | H : no_mut <{& _ :: & _      }> |- _ => tt H
  | H : no_mut <{& _ :: (_ --> _)}> |- _ => tt H
  | H : no_mut <{new _ _         }> |- _ => tt H
  | H : no_mut <{* _             }> |- _ => tt H
  | H : no_mut <{_ = _           }> |- _ => tt H
  (* irrelevant for var       *)
  | H : no_mut <{fn _ _ _        }> |- _ => tt H
  | H : no_mut <{call _ _        }> |- _ => tt H
  | H : no_mut <{_ ; _           }> |- _ => tt H
  | H : no_mut <{spawn _         }> |- _ => tt H
  end.

Ltac inv_nomut  := match_nomut inv.
Ltac invc_nomut := match_nomut invc.

(* ------------------------------------------------------------------------- *)
(* safe-spawns inversion                                                     *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_ss tt :=
  match goal with
  (* irrelevant for unit *)
  (* irrelevant for num  *)
  (* irrelevant for ad   *)
  | H : safe_spawns <{new _ _ }> |- _ => tt H
  | H : safe_spawns <{* _     }> |- _ => tt H
  | H : safe_spawns <{_ = _   }> |- _ => tt H
  (* irrelevant for var  *)
  | H : safe_spawns <{fn _ _ _}> |- _ => tt H
  | H : safe_spawns <{call _ _}> |- _ => tt H
  | H : safe_spawns <{_ ; _   }> |- _ => tt H
  | H : safe_spawns <{spawn _ }> |- _ => tt H
  end.

Ltac inv_ss  := match_ss inv.
Ltac invc_ss := match_ss invc.

(* ------------------------------------------------------------------------- *)
(* has-var inversion                                                         *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_hasvar tt :=
  match goal with
  | H : has_var _  thread_default |- _ => tt H
  | H : has_var _  <{unit    }>   |- _ => tt H
  | H : has_var _  <{N _     }>   |- _ => tt H
  | H : has_var _  <{& _ :: _}>   |- _ => tt H
  | H : has_var _  <{new _ _ }>   |- _ => tt H
  | H : has_var _  <{* _     }>   |- _ => tt H
  | H : has_var _  <{_ = _   }>   |- _ => tt H
  | H : has_var ?x <{var ?x  }>   |- _ => fail
  | H : has_var ?x <{var ?y  }>   |- _ => tt H
  | H : has_var _  <{fn _ _ _}>   |- _ => tt H
  | H : has_var _  <{call _ _}>   |- _ => tt H
  | H : has_var _  <{_ ; _   }>   |- _ => tt H
  | H : has_var _  <{spawn _ }>   |- _ => tt H
  end.

Ltac inv_hasvar  := match_hasvar inv.
Ltac invc_hasvar := match_hasvar invc.
*)

