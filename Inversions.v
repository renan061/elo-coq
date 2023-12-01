From Elo Require Import Core.
From Elo Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(* unfold hints                                                              *)
(* ------------------------------------------------------------------------- *)

#[export] Hint Unfold well_typed_term : wtt.
#[export] Hint Unfold safe_access     : sacc.

#[export] Hint Extern 4 => unfold well_typed_term : wtt.
#[export] Hint Extern 4 => unfold safe_access     : sacc.

(* ------------------------------------------------------------------------- *)
(* valid-addresses inversion                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_vad tactic :=
  match goal with
  (* irrelevant for unit *)
  (* irrelevant for num  *)
  | H : valid_addresses _ <{& _ :: _}> |- _ => tactic H
  | H : valid_addresses _ <{new _ _ }> |- _ => tactic H
  | H : valid_addresses _ <{* _     }> |- _ => tactic H
  | H : valid_addresses _ <{_ = _   }> |- _ => tactic H
  (* irrelevant for var  *)
  | H : valid_addresses _ <{fn _ _ _}> |- _ => tactic H
  | H : valid_addresses _ <{call _ _}> |- _ => tactic H
  | H : valid_addresses _ <{_ ; _   }> |- _ => tactic H
  | H : valid_addresses _ <{spawn _ }> |- _ => tactic H
  end.

Ltac inv_vad  := match_vad inv.
Ltac invc_vad := match_vad invc.

(* ------------------------------------------------------------------------- *)
(* well-typed-term inversion                                                 *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_wtt_inversion := 
  intros * [? ?]; try split; inv_type; try discriminate; eauto; eexists; eauto.

Local Lemma inv_wtt_ref : forall ad T,
  well_typed_term <{&ad :: T}> ->
  (exists T', T = <{{&T'}}>) \/ (exists T', T = <{{i&T'}}>).
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_new : forall t T,
  well_typed_term <{new T t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_load : forall t,
  well_typed_term <{*t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_asg : forall t1 t2,
  well_typed_term <{t1 = t2}> ->
  well_typed_term t1 /\ well_typed_term t2.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_var : forall x,
  well_typed_term <{var x}> ->
  False.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_fun : forall x Tx t,
  well_typed_term <{fn x Tx t}> ->
  exists T, empty[x <== Tx] |-- t is T.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_call : forall t1 t2,
  well_typed_term <{call t1 t2}> ->
  well_typed_term t1 /\ well_typed_term t2.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_seq : forall t1 t2,
  well_typed_term <{t1; t2}> ->
  well_typed_term t1 /\ well_typed_term t2.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_spawn : forall t,
  well_typed_term <{spawn t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Ltac inv_wtt :=
  match goal with
  (* irrelevant for unit *)
  (* irrelevant for num  *)
  | H : well_typed_term <{& _ :: _}> |- _ =>
      eapply inv_wtt_ref   in H as [[? ?] | [? ?]]
  | H : well_typed_term <{new _ _ }> |- _ =>
      eapply inv_wtt_new   in H
  | H : well_typed_term <{* _     }> |- _ =>
      eapply inv_wtt_load  in H
  | H : well_typed_term <{_ = _   }> |- _ =>
      eapply inv_wtt_asg   in H as [? ?]
  | H : well_typed_term <{fn _ _ _}> |- _ =>
      eapply inv_wtt_fun   in H as [? ?]
  | H : well_typed_term <{call _ _}> |- _ =>
      eapply inv_wtt_call  in H as [? ?]
  | H : well_typed_term <{_ ; _   }> |- _ =>
      eapply inv_wtt_seq   in H as [? ?]
  | H : well_typed_term <{spawn _ }> |- _ =>
      eapply inv_wtt_spawn in H
  end.

(* ------------------------------------------------------------------------- *)
(* consistently-typed-references inversion                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_ctr tactic :=
  match goal with
  (* irrelevant for unit *)
  (* irrelevant for num  *)
  | H : consistently_typed_references _ <{& _ :: _}> |- _ => tactic H
  | H : consistently_typed_references _ <{new _ _ }> |- _ => tactic H
  | H : consistently_typed_references _ <{* _     }> |- _ => tactic H
  | H : consistently_typed_references _ <{_ = _   }> |- _ => tactic H
  (* irrelevant for var  *)
  | H : consistently_typed_references _ <{fn _ _ _}> |- _ => tactic H
  | H : consistently_typed_references _ <{call _ _}> |- _ => tactic H
  | H : consistently_typed_references _ <{_ ; _   }> |- _ => tactic H
  | H : consistently_typed_references _ <{spawn _ }> |- _ => tactic H
  end.

Ltac inv_ctr  := match_ctr inv.
Ltac invc_ctr := match_ctr invc.

(* ------------------------------------------------------------------------- *)
(* access inversion                                                          *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_acc tactic :=
  match goal with
  | H : access _ _ thread_default |- _ => tactic H
  | H : access _ _ <{unit    }>   |- _ => tactic H
  | H : access _ _ <{N _     }>   |- _ => tactic H
  | H : access _ _ <{& _ :: _}>   |- _ => tactic H
  | H : access _ _ <{new _ _ }>   |- _ => tactic H
  | H : access _ _ <{* _     }>   |- _ => tactic H
  | H : access _ _ <{_ = _   }>   |- _ => tactic H
  | H : access _ _ <{var _   }>   |- _ => tactic H
  | H : access _ _ <{fn _ _ _}>   |- _ => tactic H
  | H : access _ _ <{call _ _}>   |- _ => tactic H
  | H : access _ _ <{_ ; _   }>   |- _ => tactic H
  | H : access _ _ <{spawn _ }>   |- _ => tactic H
  end.

Ltac inv_acc  := match_acc inv.
Ltac invc_acc := match_acc invc.

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
(* unsafe-access inversion                                                   *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_uacc tactic :=
  match goal with
  | H : unsafe_access _ _ thread_default |- _ => tactic H
  | H : unsafe_access _ _ <{unit    }>   |- _ => tactic H
  | H : unsafe_access _ _ <{N _     }>   |- _ => tactic H
  | H : unsafe_access _ _ <{& _ :: _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{new _ _ }>   |- _ => tactic H
  | H : unsafe_access _ _ <{* _     }>   |- _ => tactic H
  | H : unsafe_access _ _ <{_ = _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{var _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{fn _ _ _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{call _ _}>   |- _ => tactic H
  | H : unsafe_access _ _ <{_ ; _   }>   |- _ => tactic H
  | H : unsafe_access _ _ <{spawn _ }>   |- _ => tactic H
  end.

Ltac inv_uacc  := match_uacc inv.
Ltac invc_uacc := match_uacc invc.

(* ------------------------------------------------------------------------- *)
(* not-unsafe-access inversion                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma inv_nuacc_ref_eq : forall m ad T,
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

Local Lemma inv_nuacc_new : forall m t ad T,
  ~ unsafe_access ad m <{new T t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_load : forall m t ad,
  ~ unsafe_access ad m <{*t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_asg : forall m t1 t2 ad,
  ~ unsafe_access ad m <{t1 = t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_fun : forall m t ad x Tx,
  ~ unsafe_access ad m <{fn x Tx t}> ->
  ~ unsafe_access ad m t.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_call : forall m t1 t2 ad,
  ~ unsafe_access ad m <{call t1 t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Local Lemma inv_nuacc_seq : forall m t1 t2 ad,
  ~ unsafe_access ad m <{t1; t2}> ->
  ~ unsafe_access ad m t1 /\ ~ unsafe_access ad m t2.
Proof. solve_nuacc_inversion. Qed.

Ltac inv_nuacc :=
  match goal with
  | H : ~ unsafe_access ?ad _ <{& ?ad  :: & _ }> |- _ =>
    eapply inv_nuacc_ref_eq   in H; solve contradiction
  | H : ~ unsafe_access ?ad _ <{& ?ad' :: & _ }> |- _ =>
    eapply inv_nuacc_ref_neqM in H as [? ?]
  | H : ~ unsafe_access _ _   <{new _ _       }> |- _ =>
    eapply inv_nuacc_new     in H
  | H : ~ unsafe_access _ _   <{* _           }> |- _ =>
    eapply inv_nuacc_load    in H
  | H : ~ unsafe_access _ _   <{_ = _         }> |- _ =>
    eapply inv_nuacc_asg     in H as [? ?]
  | H : ~ unsafe_access _ _   <{fn _ _ _      }> |- _ =>
    eapply inv_nuacc_fun     in H
  | H : ~ unsafe_access _ _   <{call _ _      }> |- _ =>
    eapply inv_nuacc_call    in H as [? ?]
  | H : ~ unsafe_access _ _   <{_ ; _         }> |- _ =>
    eapply inv_nuacc_seq     in H as [? ?]

  | Hval   : forall_memory ?m value,
    Hctr   : consistently_typed_references ?m <{& ?ad' :: (i& ?T) }>,
    Hnuacc : ~ unsafe_access ?ad ?m <{& ?ad' :: (i& ?T) }> |- _ =>
    eapply (inv_nuacc_ref_neqI m ad ad' T Hval Hctr) in Hnuacc
  end.

(* ------------------------------------------------------------------------- *)
(* no-mut inversion                                                          *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_nomut tactic :=
  match goal with
  (* irrelevant for unit      *)
  (* irrelevant for num       *)
  | H : no_mut <{& _ :: Unit     }> |- _ => tactic H
  | H : no_mut <{& _ :: Num      }> |- _ => tactic H
  (* irrelevant if &ad :: i&T *)
  | H : no_mut <{& _ :: & _      }> |- _ => tactic H
  | H : no_mut <{& _ :: (_ --> _)}> |- _ => tactic H
  | H : no_mut <{new _ _         }> |- _ => tactic H
  | H : no_mut <{* _             }> |- _ => tactic H
  | H : no_mut <{_ = _           }> |- _ => tactic H
  (* irrelevant for var       *)
  | H : no_mut <{fn _ _ _        }> |- _ => tactic H
  | H : no_mut <{call _ _        }> |- _ => tactic H
  | H : no_mut <{_ ; _           }> |- _ => tactic H
  | H : no_mut <{spawn _         }> |- _ => tactic H
  end.

Ltac inv_nomut  := match_nomut inv.
Ltac invc_nomut := match_nomut invc.

(* ------------------------------------------------------------------------- *)
(* safe-spawns inversion                                                     *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_ss tactic :=
  match goal with
  (* irrelevant for unit *)
  (* irrelevant for num  *)
  (* irrelevant for ad   *)
  | H : safe_spawns <{new _ _ }> |- _ => tactic H
  | H : safe_spawns <{* _     }> |- _ => tactic H
  | H : safe_spawns <{_ = _   }> |- _ => tactic H
  (* irrelevant for var  *)
  | H : safe_spawns <{fn _ _ _}> |- _ => tactic H
  | H : safe_spawns <{call _ _}> |- _ => tactic H
  | H : safe_spawns <{_ ; _   }> |- _ => tactic H
  | H : safe_spawns <{spawn _ }> |- _ => tactic H
  end.

Ltac inv_ss  := match_ss inv.
Ltac invc_ss := match_ss invc.

(* ------------------------------------------------------------------------- *)
(* has-var inversion                                                         *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_hasvar tactic :=
  match goal with
  | H : has_var _  thread_default |- _ => tactic H
  | H : has_var _  <{unit    }>   |- _ => tactic H
  | H : has_var _  <{N _     }>   |- _ => tactic H
  | H : has_var _  <{& _ :: _}>   |- _ => tactic H
  | H : has_var _  <{new _ _ }>   |- _ => tactic H
  | H : has_var _  <{* _     }>   |- _ => tactic H
  | H : has_var _  <{_ = _   }>   |- _ => tactic H
  | H : has_var ?x <{var ?x  }>   |- _ => fail
  | H : has_var ?x <{var ?y  }>   |- _ => tactic H
  | H : has_var _  <{fn _ _ _}>   |- _ => tactic H
  | H : has_var _  <{call _ _}>   |- _ => tactic H
  | H : has_var _  <{_ ; _   }>   |- _ => tactic H
  | H : has_var _  <{spawn _ }>   |- _ => tactic H
  end.

Ltac inv_hasvar  := match_hasvar inv.
Ltac invc_hasvar := match_hasvar invc.

