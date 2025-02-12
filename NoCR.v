From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-cr                                                                     *)
(* ------------------------------------------------------------------------- *)

(*
  (!!!) no-cr is an initial condition.
*)
Inductive no_cr (ad : addr) : tm -> Prop :=
  | nocr_unit  :                  no_cr ad <{unit                     }>
  | nocr_nat   : forall n,        no_cr ad <{nat n                    }>
  | nocr_plus  : forall t1 t2,    no_cr ad t1 ->
                                  no_cr ad t2 ->
                                  no_cr ad <{t1 + t2                  }>
  | nocr_monus : forall t1 t2,    no_cr ad t1 ->
                                  no_cr ad t2 ->
                                  no_cr ad <{t1 - t2                  }>
  | nocr_seq   : forall t1 t2,    no_cr ad t1 ->
                                  no_cr ad t2 ->
                                  no_cr ad <{t1; t2                   }>
  | nocr_if    : forall t1 t2 t3, no_cr ad t1 ->
                                  no_cr ad t2 ->
                                  no_cr ad t3 ->
                                  no_cr ad <{if t1 then t2 else t3 end}>
  | nocr_while : forall t1 t2,    no_cr ad t1 ->
                                  no_cr ad t2 ->
                                  no_cr ad <{while t1 do t2 end       }>
  | nocr_var   : forall x,        no_cr ad <{var x                    }>
  | nocr_fun   : forall x Tx t,   no_cr ad t  ->
                                  no_cr ad <{fn x Tx t                }>
  | nocr_call  : forall t1 t2,    no_cr ad t1 ->
                                  no_cr ad t2 ->
                                  no_cr ad <{call t1 t2               }>
  | nocr_ref   : forall ad' T,    no_cr ad <{&ad' : T                 }>
  | nocr_new   : forall t T,      no_cr ad t  ->
                                  no_cr ad <{new t : T                }>
  | nocr_init  : forall ad' t T,  no_cr ad t  ->
                                  no_cr ad <{init ad' t : T           }>
  | nocr_load  : forall t,        no_cr ad t  ->
                                  no_cr ad <{*t                       }>
  | nocr_asg   : forall t1 t2,    no_cr ad t1 ->
                                  no_cr ad t2 ->
                                  no_cr ad <{t1 := t2                 }>
  | nocr_acq   : forall t1 x t2,  no_cr ad t1 ->
                                  no_cr ad t2 ->
                                  no_cr ad <{acq t1 x t2              }>
  | nocr_cr    : forall ad' t,    ad <> ad'   ->
                                  no_cr ad t  ->
                                  no_cr ad <{cr ad' t                 }>
  | nocr_wait  : forall t,        no_cr ad t  ->
                                  no_cr ad <{wait t                   }>
  | nocr_reacq : forall ad',      no_cr ad <{reacq ad'                }>
  | nocr_spawn : forall t,        no_cr ad t  ->
                                  no_cr ad <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _nocr tt :=
  match goal with
  | H : no_cr _   <{unit                  }> |- _ => clear H
  | H : no_cr _   <{nat _                 }> |- _ => clear H
  | H : no_cr _   <{_ + _                 }> |- _ => tt H
  | H : no_cr _   <{_ - _                 }> |- _ => tt H
  | H : no_cr _   <{_; _                  }> |- _ => tt H
  | H : no_cr _   <{if _ then _ else _ end}> |- _ => tt H
  | H : no_cr _   <{while _ do _ end      }> |- _ => tt H
  | H : no_cr _   <{var _                 }> |- _ => clear H
  | H : no_cr _   <{fn _ _ _              }> |- _ => tt H
  | H : no_cr _   <{call _ _              }> |- _ => tt H
  | H : no_cr _   <{&_ : _                }> |- _ => clear H
  | H : no_cr _   <{new _ : _             }> |- _ => tt H
  | H : no_cr _   <{init _ _ : _          }> |- _ => tt H
  | H : no_cr _   <{* _                   }> |- _ => tt H
  | H : no_cr _   <{_ := _                }> |- _ => tt H
  | H : no_cr _   <{acq _ _ _             }> |- _ => tt H
  | H : no_cr ?ad <{cr ?ad _              }> |- _ => invc H; auto
  | H : no_cr _   <{cr _ _                }> |- _ => tt H
  | H : no_cr _   <{wait _                }> |- _ => tt H
  | H : no_cr _   <{reacq _               }> |- _ => clear H
  | H : no_cr _   <{spawn _               }> |- _ => tt H
  end.

Ltac inv_nocr  := _nocr inv.
Ltac invc_nocr := _nocr invc.

(* decidability ------------------------------------------------------------ *)

Lemma nocr_dec : forall ad t,
  Decidable.decidable (no_cr ad t).
Proof.
  unfold Decidable.decidable. unfold not. intros.
  induction t; auto using no_cr;
  (destruct IHt1, IHt2, IHt3 || destruct IHt1, IHt2 || destruct IHt);
  auto using no_cr;
  try solve [right; intros; invc_nocr; auto].
  match goal with ad1 : addr, ad2 : addr |- _ => nat_eq_dec ad1 ad2 end;
  auto using no_cr. right. intros. invc_nocr.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma nocr_acq_contradiction : forall t1 t2 ad t,
  no_cr ad t2 ->
  t1 --[e_acq ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_nocr; auto.
Qed.

Lemma nocr_rel_contradiction : forall t1 t2 ad,
  no_cr ad t1 ->
  t1 --[e_rel ad]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_nocr; auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma nocr_subst : forall ad x tx t,
  no_cr ad t ->
  no_cr ad tx ->
  no_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; simpl; repeat destruct _str_eq_dec;
  invc_nocr; auto using no_cr.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_nocr_preservation :=
  intros; ind_tstep; repeat invc_nocr; auto using nocr_subst, no_cr.

Lemma nocr_preservation_none : forall ad t1 t2,
  no_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_alloc : forall ad t1 t2 ad' T',
  no_cr ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_init : forall ad t1 t2 ad' t',
  no_cr ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_read : forall ad t1 t2 ad' t',
  no_cr ad t' ->
  (* --- *)
  no_cr ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_write : forall ad t1 t2 ad' t',
  no_cr ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_acq : forall ad t1 t2 ad' t',
  no_cr ad t' ->
  (* --- *)
  ad <> ad' ->
  no_cr ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_rel : forall ad t1 t2 ad',
  no_cr ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_wacq : forall ad t1 t2 ad',
  no_cr ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_wrel : forall ad t1 t2 ad',
  no_cr ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_spawn : forall ad t1 t2 t',
  no_cr ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_spawned : forall ad t1 t2 t',
  no_cr ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  no_cr ad t'.
Proof. solve_nocr_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* no-crs                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition no_crs (t : tm) := forall ad, no_cr ad t.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_nocrs :=
  unfold no_crs; intros * H; repeat split; intros; spec; invc_nocr; auto.

Local Lemma inv_nocrs_plus : forall t1 t2,
  no_crs <{t1 + t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_monus : forall t1 t2,
  no_crs <{t1 - t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_seq : forall t1 t2,
  no_crs <{t1; t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_if : forall t1 t2 t3,
  no_crs (tm_if t1 t2 t3) -> no_crs t1 /\ no_crs t2 /\ no_crs t3.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_while : forall t1 t2,
  no_crs <{while t1 do t2 end}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_fun : forall x Tx t,
  no_crs <{fn x Tx t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_call : forall t1 t2,
  no_crs <{call t1 t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_new : forall t T,
  no_crs <{new t : T}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_init : forall ad t T,
  no_crs <{init ad t : T}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_load : forall t,
  no_crs <{*t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_asg : forall t1 t2,
  no_crs <{t1 := t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_acq : forall t1 x t2,
  no_crs <{acq t1 x t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_cr : forall ad t,
  no_crs <{cr ad t}> -> False.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_wait : forall t,
  no_crs <{wait t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_spawn : forall t,
  no_crs <{spawn t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Ltac invc_nocrs :=
  match goal with
  | H : no_crs <{unit        }> |- _ => clear H
  | H : no_crs <{nat _       }> |- _ => clear H
  | H : no_crs <{_ + _       }> |- _ => eapply inv_nocrs_plus  in H
  | H : no_crs <{_ - _       }> |- _ => eapply inv_nocrs_monus in H
  | H : no_crs <{_; _        }> |- _ => eapply inv_nocrs_seq   in H
  | H : no_crs (tm_if _ _ _  )  |- _ => eapply inv_nocrs_if    in H
  | H : no_crs (tm_while _ _ )  |- _ => eapply inv_nocrs_while in H
  | H : no_crs <{var _       }> |- _ => clear H
  | H : no_crs <{fn _ _ _    }> |- _ => eapply inv_nocrs_fun   in H
  | H : no_crs <{call _ _    }> |- _ => eapply inv_nocrs_call  in H
  | H : no_crs <{& _ : _     }> |- _ => clear H
  | H : no_crs <{new _ : _   }> |- _ => eapply inv_nocrs_new   in H
  | H : no_crs <{init _ _ : _}> |- _ => eapply inv_nocrs_init  in H
  | H : no_crs <{* _         }> |- _ => eapply inv_nocrs_load  in H
  | H : no_crs <{_ := _      }> |- _ => eapply inv_nocrs_asg   in H
  | H : no_crs <{acq _ _ _   }> |- _ => eapply inv_nocrs_acq   in H
  | H : no_crs <{cr _ _      }> |- _ => eapply inv_nocrs_cr    in H; auto
  | H : no_crs <{wait _      }> |- _ => eapply inv_nocrs_wait  in H
  | H : no_crs <{reacq _     }> |- _ => clear H
  | H : no_crs <{spawn _     }> |- _ => eapply inv_nocrs_spawn in H
  end;
  repeat match goal with
  | H : no_crs _ /\ no_crs _             |- _ => destruct H
  | H : no_crs _ /\ no_crs _ /\ no_crs _ |- _ => destruct H as [? [? ?]]
  end.

(* lemmas ------------------------------------------------------------------ *)

Corollary nocr_from_nocrs : forall ad t,
  no_crs t ->
  no_cr ad t.
Proof.
  unfold no_crs. trivial.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Corollary nocrs_subst : forall x tx t,
  no_crs t ->
  no_crs tx ->
  no_crs <{[x := tx] t}>.
Proof.
  intros ** ?. auto using nocr_subst.
Qed.

