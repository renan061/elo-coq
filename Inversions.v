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

