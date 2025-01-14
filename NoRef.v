From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-ref                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive no_ref (ad : addr) : tm -> Prop :=
  | noref_unit  :                  no_ref ad <{unit                     }>
  | noref_nat   : forall n,        no_ref ad <{nat n                    }>
  | noref_plus  : forall t1 t2,    no_ref ad t1 ->
                                   no_ref ad t2 ->
                                   no_ref ad <{t1 + t2                  }>
  | noref_monus : forall t1 t2,    no_ref ad t1 ->
                                   no_ref ad t2 ->
                                   no_ref ad <{t1 - t2                  }>
  | noref_seq   : forall t1 t2,    no_ref ad t1 ->
                                   no_ref ad t2 ->
                                   no_ref ad <{t1; t2                   }>
  | noref_if    : forall t1 t2 t3, no_ref ad t1 ->
                                   no_ref ad t2 ->
                                   no_ref ad t3 ->
                                   no_ref ad <{if t1 then t2 else t3 end}>
  | noref_while : forall t1 t2,    no_ref ad t1 ->
                                   no_ref ad t2 ->
                                   no_ref ad <{while t1 do t2 end       }>
  | noref_var   : forall x,        no_ref ad <{var x                    }>
  | noref_fun   : forall x Tx t,   no_ref ad t  ->
                                   no_ref ad <{fn x Tx t                }>
  | noref_call  : forall t1 t2,    no_ref ad t1 ->
                                   no_ref ad t2 ->
                                   no_ref ad <{call t1 t2               }>
  | noref_ref   : forall ad' T,    ad <> ad'    ->
                                   no_ref ad <{&ad' : T                 }>
  | noref_new   : forall t T,      no_ref ad t  ->
                                   no_ref ad <{new t : T                }>
  | noref_init  : forall ad' t T,  no_ref ad t  ->
                                   no_ref ad <{init ad' t : T           }>
  | noref_load  : forall t,        no_ref ad t  ->
                                   no_ref ad <{*t                       }>
  | noref_asg   : forall t1 t2,    no_ref ad t1 ->
                                   no_ref ad t2 ->
                                   no_ref ad <{t1 := t2                 }>
  | noref_acq   : forall t1 x t2,  no_ref ad t1 ->
                                   no_ref ad t2 ->
                                   no_ref ad <{acq t1 x t2              }>
  | noref_cr    : forall ad' t,    no_ref ad t  ->
                                   no_ref ad <{cr ad' t                 }>
  | noref_wait  : forall ad',      no_ref ad <{wait ad'                 }>
  | noref_reacq : forall ad',      no_ref ad <{reacq ad'                }>
  | noref_spawn : forall t,        no_ref ad t ->
                                   no_ref ad <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _noref tt :=
  match goal with
  | H : no_ref _   <{unit                  }> |- _ => clear H
  | H : no_ref _   <{nat _                 }> |- _ => clear H
  | H : no_ref _   <{_ + _                 }> |- _ => tt H
  | H : no_ref _   <{_ - _                 }> |- _ => tt H
  | H : no_ref _   <{_; _                  }> |- _ => tt H
  | H : no_ref _   <{if _ then _ else _ end}> |- _ => tt H
  | H : no_ref _   <{while _ do _ end      }> |- _ => tt H
  | H : no_ref _   <{var _                 }> |- _ => clear H
  | H : no_ref _   <{fn _ _ _              }> |- _ => tt H
  | H : no_ref _   <{call _ _              }> |- _ => tt H
  | H : no_ref ?ad <{& ?ad : _             }> |- _ => invc H; auto
  | H : no_ref _   <{&_ : _                }> |- _ => tt H
  | H : no_ref _   <{new _ : _             }> |- _ => tt H
  | H : no_ref _   <{init _ _ : _          }> |- _ => tt H
  | H : no_ref _   <{* _                   }> |- _ => tt H
  | H : no_ref _   <{_ := _                }> |- _ => tt H
  | H : no_ref _   <{acq _ _ _             }> |- _ => tt H
  | H : no_ref _   <{cr _ _                }> |- _ => tt H
  | H : no_ref _   <{wait _                }> |- _ => clear H
  | H : no_ref _   <{reacq _               }> |- _ => clear H
  | H : no_ref _   <{spawn _               }> |- _ => tt H
  end.

Ltac inv_noref  := _noref inv.
Ltac invc_noref := _noref invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma noref_init_term : forall m t1 t2 ad t,
  no_ref m t1 ->
  t1 --[e_init ad t]--> t2 ->
  no_ref m t.
Proof.
  intros. ind_tstep; invc_noref; auto.
Qed.

Lemma noref_write_term : forall m t1 t2 ad t,
  no_ref m t1 ->
  t1 --[e_write ad t]--> t2 ->
  no_ref m t.
Proof.
  intros. ind_tstep; invc_noref; auto.
Qed.

Lemma noref_write_contradiction : forall t1 t2 ad t,
  no_ref ad t1 ->
  t1 --[e_write ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_noref; auto.
Qed.

Lemma noref_acq_contradiction : forall t1 t2 ad t,
  no_ref ad t1 ->
  t1 --[e_acq ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_noref; auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma noref_subst : forall ad x tx t,
  no_ref ad t ->
  no_ref ad tx ->
  no_ref ad <{[x := tx] t}>.
Proof. 
  intros. induction t; invc_noref;
  simpl in *; try destruct _str_eq_dec; auto using no_ref.
Qed.

Lemma noref_fw : forall ad ad' t,
  no_ref ad t ->
  no_ref ad (fw ad' t).
Proof. 
  intros. induction t; invc_noref; simpl; auto using no_ref.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_noref_preservation :=
  intros; ind_tstep; repeat invc_noref;
  auto using noref_subst, noref_fw, no_ref.

Lemma noref_preservation_none : forall ad t1 t2,
  no_ref ad t1 ->
  t1 --[e_none]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_alloc : forall ad t1 t2 ad' T',
  no_ref ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_init : forall ad t1 t2 ad' t',
  ad <> ad' ->
  no_ref ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_read : forall ad t1 t2 ad' t',
  no_ref ad t' ->
  (* --- *)
  no_ref ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_write : forall ad t1 t2 ad' t',
  no_ref ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_acq : forall ad t1 t2 ad' t',
  no_ref ad t' ->
  (* --- *)
  no_ref ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_rel : forall ad t1 t2 ad',
  no_ref ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_wacq : forall ad t1 t2 ad',
  no_ref ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_wrel : forall ad t1 t2 ad',
  no_ref ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_spawn : forall ad t1 t2 tid' t',
  no_ref ad t1 ->
  t1 --[e_spawn tid' t']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_spawned : forall ad t1 t2 tid' t',
  no_ref ad t1 ->
  t1 --[e_spawn tid' t']--> t2 ->
  no_ref ad t'.
Proof. solve_noref_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* no-refs                                                                   *)
(* ------------------------------------------------------------------------- *)

Definition no_refs (t : tm) := forall ad, no_ref ad t.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_norefs :=
  unfold no_refs; intros; repeat split; intros; spec; invc_noref; auto.

Local Lemma inv_norefs_plus : forall t1 t2,
  no_refs <{t1 + t2}> -> no_refs t1 /\ no_refs t2.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_monus : forall t1 t2,
  no_refs <{t1 - t2}> -> no_refs t1 /\ no_refs t2.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_seq : forall t1 t2,
  no_refs <{t1; t2}> -> no_refs t1 /\ no_refs t2.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_if : forall t1 t2 t3,
  no_refs (tm_if t1 t2 t3) -> no_refs t1 /\ no_refs t2 /\ no_refs t3.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_while : forall t1 t2,
  no_refs <{while t1 do t2 end}> -> no_refs t1 /\ no_refs t2.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_fun : forall x Tx t,
  no_refs <{fn x Tx t}> -> no_refs t.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_call : forall t1 t2,
  no_refs <{call t1 t2}> -> no_refs t1 /\ no_refs t2.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_ref : forall ad T,
  no_refs <{&ad : T}> -> False.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_new : forall t T,
  no_refs <{new t : T}> -> no_refs t.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_init : forall ad t T,
  no_refs <{init ad t : T}> -> no_refs t.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_load : forall t,
  no_refs <{*t}> -> no_refs t.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_asg : forall t1 t2,
  no_refs <{t1 := t2}> -> no_refs t1 /\ no_refs t2.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_acq : forall t1 x t2,
  no_refs <{acq t1 x t2}> -> no_refs t1 /\ no_refs t2.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_cr : forall ad t,
  no_refs <{cr ad t}> -> no_refs t.
Proof. solve_inv_norefs. Qed.

Local Lemma inv_norefs_spawn : forall t,
  no_refs <{spawn t}> -> no_refs t.
Proof. solve_inv_norefs. Qed.

Ltac invc_norefs :=
  match goal with
  | H : no_refs <{unit        }> |- _ => clear H
  | H : no_refs <{nat _       }> |- _ => clear H
  | H : no_refs <{_ + _       }> |- _ => eapply inv_norefs_plus  in H
  | H : no_refs <{_ - _       }> |- _ => eapply inv_norefs_monus in H
  | H : no_refs <{_; _        }> |- _ => eapply inv_norefs_seq   in H
  | H : no_refs (tm_if _ _ _  )  |- _ => eapply inv_norefs_if    in H
  | H : no_refs (tm_while _ _ )  |- _ => eapply inv_norefs_while in H
  | H : no_refs <{var _       }> |- _ => clear H
  | H : no_refs <{fn _ _ _    }> |- _ => eapply inv_norefs_fun   in H
  | H : no_refs <{call _ _    }> |- _ => eapply inv_norefs_call  in H
  | H : no_refs <{& _ : _     }> |- _ => eapply inv_norefs_ref   in H; auto
  | H : no_refs <{new _ : _   }> |- _ => eapply inv_norefs_new   in H
  | H : no_refs <{init _ _ : _}> |- _ => eapply inv_norefs_init  in H
  | H : no_refs <{* _         }> |- _ => eapply inv_norefs_load  in H
  | H : no_refs <{_ := _      }> |- _ => eapply inv_norefs_asg   in H
  | H : no_refs <{acq _ _ _   }> |- _ => eapply inv_norefs_acq   in H
  | H : no_refs <{cr _ _      }> |- _ => eapply inv_norefs_cr    in H
  | H : no_refs <{wait _      }> |- _ => clear H
  | H : no_refs <{reacq _     }> |- _ => clear H
  | H : no_refs <{spawn _     }> |- _ => eapply inv_norefs_spawn in H
  end;
  repeat match goal with
  | H : no_refs _ /\ no_refs _              |- _ => destruct H
  | H : no_refs _ /\ no_refs _ /\ no_refs _ |- _ => destruct H as [? [? ?]]
  end.

