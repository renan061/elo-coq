From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-reacq                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive no_reacq (ad : addr) : tm -> Prop :=
  | noreacq_unit  :                  no_reacq ad <{unit                     }>
  | noreacq_nat   : forall n,        no_reacq ad <{nat n                    }>
  | noreacq_plus  : forall t1 t2,    no_reacq ad t1 ->
                                     no_reacq ad t2 ->
                                     no_reacq ad <{t1 + t2                  }>
  | noreacq_monus : forall t1 t2,    no_reacq ad t1 ->
                                     no_reacq ad t2 ->
                                     no_reacq ad <{t1 - t2                  }>
  | noreacq_seq   : forall t1 t2,    no_reacq ad t1 ->
                                     no_reacq ad t2 ->
                                     no_reacq ad <{t1; t2                   }>
  | noreacq_if    : forall t1 t2 t3, no_reacq ad t1 ->
                                     no_reacq ad t2 ->
                                     no_reacq ad t3 ->
                                     no_reacq ad <{if t1 then t2 else t3 end}>
  | noreacq_while : forall t1 t2,    no_reacq ad t1 ->
                                     no_reacq ad t2 ->
                                     no_reacq ad <{while t1 do t2 end       }>
  | noreacq_var   : forall x,        no_reacq ad <{var x                    }>
  | noreacq_fun   : forall x Tx t,   no_reacq ad t  ->
                                     no_reacq ad <{fn x Tx t                }>
  | noreacq_call  : forall t1 t2,    no_reacq ad t1 ->
                                     no_reacq ad t2 ->
                                     no_reacq ad <{call t1 t2               }>
  | noreacq_ref   : forall ad' T,    no_reacq ad <{&ad' : T                 }>
  | noreacq_new   : forall t T,      no_reacq ad t  ->
                                     no_reacq ad <{new t : T                }>
  | noreacq_init  : forall ad' t T,  no_reacq ad t  ->
                                     no_reacq ad <{init ad' t : T           }>
  | noreacq_load  : forall t,        no_reacq ad t  ->
                                     no_reacq ad <{*t                       }>
  | noreacq_asg   : forall t1 t2,    no_reacq ad t1 ->
                                     no_reacq ad t2 ->
                                     no_reacq ad <{t1 := t2                 }>
  | noreacq_acq   : forall t1 x t2,  no_reacq ad t1 ->
                                     no_reacq ad t2 ->
                                     no_reacq ad <{acq t1 x t2              }>
  | noreacq_cr    : forall ad' t,    no_reacq ad t  ->
                                     no_reacq ad <{cr ad' t                 }>
  | noreacq_wait  : forall t,        no_reacq ad t  ->
                                     no_reacq ad <{wait t                   }>
  | noreacq_reacq : forall ad',      ad <> ad'      ->
                                     no_reacq ad <{reacq ad'                }>
  | noreacq_spawn : forall t,        no_reacq ad t ->
                                     no_reacq ad <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _noreacq tt :=
  match goal with
  | H : no_reacq _   <{unit                  }> |- _ => clear H
  | H : no_reacq _   <{nat _                 }> |- _ => clear H
  | H : no_reacq _   <{_ + _                 }> |- _ => tt H
  | H : no_reacq _   <{_ - _                 }> |- _ => tt H
  | H : no_reacq _   <{_; _                  }> |- _ => tt H
  | H : no_reacq _   <{if _ then _ else _ end}> |- _ => tt H
  | H : no_reacq _   <{while _ do _ end      }> |- _ => tt H
  | H : no_reacq _   <{var _                 }> |- _ => clear H
  | H : no_reacq _   <{fn _ _ _              }> |- _ => tt H
  | H : no_reacq _   <{call _ _              }> |- _ => tt H
  | H : no_reacq _   <{&_ : _                }> |- _ => tt H
  | H : no_reacq _   <{new _ : _             }> |- _ => tt H
  | H : no_reacq _   <{init _ _ : _          }> |- _ => tt H
  | H : no_reacq _   <{* _                   }> |- _ => tt H
  | H : no_reacq _   <{_ := _                }> |- _ => tt H
  | H : no_reacq _   <{acq _ _ _             }> |- _ => tt H
  | H : no_reacq _   <{cr _ _                }> |- _ => tt H
  | H : no_reacq _   <{wait _                }> |- _ => tt H
  | H : no_reacq ?ad <{reacq ?ad             }> |- _ => invc H; auto
  | H : no_reacq _   <{reacq _               }> |- _ => tt H
  | H : no_reacq _   <{spawn _               }> |- _ => tt H
  end.

Ltac inv_noreacq  := _noreacq inv.
Ltac invc_noreacq := _noreacq invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma noreacq_wacq_contradiction : forall t1 t2 ad,
  no_reacq ad t1 ->
  t1 --[e_wacq ad]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_noreacq; auto.
Qed.

Lemma noreacq_wrel_contradiction : forall t1 t2 ad,
  no_reacq ad t2 ->
  t1 --[e_wrel ad]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_noreacq; auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma noreacq_subst : forall ad x tx t,
  no_reacq ad t ->
  no_reacq ad tx ->
  no_reacq ad <{[x := tx] t}>.
Proof.
  intros. induction t; simpl; repeat destruct _str_eq_dec;
  invc_noreacq; auto using no_reacq.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_noreacq_preservation :=
  intros; ind_tstep; repeat invc_noreacq; auto using noreacq_subst, no_reacq.

Lemma noreacq_preservation_none : forall ad t1 t2,
  no_reacq ad t1 ->
  t1 --[e_none]--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_alloc : forall ad t1 t2 ad' T',
  no_reacq ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_init : forall ad t1 t2 ad' t',
  no_reacq ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_read : forall ad t1 t2 ad' t',
  no_reacq ad t' ->
  (* --- *)
  no_reacq ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_write : forall ad t1 t2 ad' t',
  no_reacq ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_acq : forall ad t1 t2 ad' t',
  no_reacq ad t' ->
  (* --- *)
  no_reacq ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_rel : forall ad t1 t2 ad',
  no_reacq ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_wacq : forall ad t1 t2 ad',
  no_reacq ad t1 ->
  t1 --[e_wacq ad']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_wrel : forall ad t1 t2 ad',
  ad <> ad' ->
  no_reacq ad t1 ->
  t1 --[e_wrel ad']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_spawn : forall ad t1 t2 t',
  no_reacq ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  no_reacq ad t2.
Proof. solve_noreacq_preservation. Qed.

Lemma noreacq_preservation_spawned : forall ad t1 t2 t',
  no_reacq ad t1 ->
  t1 --[e_spawn t']--> t2 ->
  no_reacq ad t'.
Proof. solve_noreacq_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* no-reacqs                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
  (!!!) no-reacqs is an initial condition.
*)
Definition no_reacqs (t : tm) := forall ad, no_reacq ad t.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_noreacqs :=
  unfold no_reacqs; intros; repeat split; intros; spec; invc_noreacq; auto.

Local Lemma inv_noreacqs_plus : forall t1 t2,
  no_reacqs <{t1 + t2}> -> no_reacqs t1 /\ no_reacqs t2.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_monus : forall t1 t2,
  no_reacqs <{t1 - t2}> -> no_reacqs t1 /\ no_reacqs t2.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_seq : forall t1 t2,
  no_reacqs <{t1; t2}> -> no_reacqs t1 /\ no_reacqs t2.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_if : forall t1 t2 t3,
  no_reacqs (tm_if t1 t2 t3) -> no_reacqs t1 /\ no_reacqs t2 /\ no_reacqs t3.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_while : forall t1 t2,
  no_reacqs <{while t1 do t2 end}> -> no_reacqs t1 /\ no_reacqs t2.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_fun : forall x Tx t,
  no_reacqs <{fn x Tx t}> -> no_reacqs t.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_call : forall t1 t2,
  no_reacqs <{call t1 t2}> -> no_reacqs t1 /\ no_reacqs t2.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_new : forall t T,
  no_reacqs <{new t : T}> -> no_reacqs t.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_init : forall ad t T,
  no_reacqs <{init ad t : T}> -> no_reacqs t.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_load : forall t,
  no_reacqs <{*t}> -> no_reacqs t.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_asg : forall t1 t2,
  no_reacqs <{t1 := t2}> -> no_reacqs t1 /\ no_reacqs t2.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_acq : forall t1 x t2,
  no_reacqs <{acq t1 x t2}> -> no_reacqs t1 /\ no_reacqs t2.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_cr : forall ad t,
  no_reacqs <{cr ad t}> -> no_reacqs t.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_wait : forall t,
  no_reacqs <{wait t}> -> no_reacqs t.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_reacq : forall ad,
  no_reacqs <{reacq ad}> -> False.
Proof. solve_inv_noreacqs. Qed.

Local Lemma inv_noreacqs_spawn : forall t,
  no_reacqs <{spawn t}> -> no_reacqs t.
Proof. solve_inv_noreacqs. Qed.

Ltac invc_noreacqs :=
 match goal with
 | H : no_reacqs <{unit        }> |- _ => clear H
 | H : no_reacqs <{nat _       }> |- _ => clear H
 | H : no_reacqs <{_ + _       }> |- _ => eapply inv_noreacqs_plus  in H
 | H : no_reacqs <{_ - _       }> |- _ => eapply inv_noreacqs_monus in H
 | H : no_reacqs <{_; _        }> |- _ => eapply inv_noreacqs_seq   in H
 | H : no_reacqs (tm_if _ _ _  )  |- _ => eapply inv_noreacqs_if    in H
 | H : no_reacqs (tm_while _ _ )  |- _ => eapply inv_noreacqs_while in H
 | H : no_reacqs <{var _       }> |- _ => clear H
 | H : no_reacqs <{fn _ _ _    }> |- _ => eapply inv_noreacqs_fun   in H
 | H : no_reacqs <{call _ _    }> |- _ => eapply inv_noreacqs_call  in H
 | H : no_reacqs <{& _ : _     }> |- _ => clear H
 | H : no_reacqs <{new _ : _   }> |- _ => eapply inv_noreacqs_new   in H
 | H : no_reacqs <{init _ _ : _}> |- _ => eapply inv_noreacqs_init  in H
 | H : no_reacqs <{* _         }> |- _ => eapply inv_noreacqs_load  in H
 | H : no_reacqs <{_ := _      }> |- _ => eapply inv_noreacqs_asg   in H
 | H : no_reacqs <{acq _ _ _   }> |- _ => eapply inv_noreacqs_acq   in H
 | H : no_reacqs <{cr _ _      }> |- _ => eapply inv_noreacqs_cr    in H
 | H : no_reacqs <{wait _      }> |- _ => eapply inv_noreacqs_wait  in H
 | H : no_reacqs <{reacq _     }> |- _ => eapply inv_noreacqs_reacq in H; auto
 | H : no_reacqs <{spawn _     }> |- _ => eapply inv_noreacqs_spawn in H
 end;
 repeat match goal with
 | H : no_reacqs _ /\ no_reacqs _                |- _ => destruct H
 | H : no_reacqs _ /\ no_reacqs _ /\ no_reacqs _ |- _ => destruct H as [? [? ?]]
 end.

(* lemmas ------------------------------------------------------------------ *)

Corollary noreacq_from_noreacqs : forall ad t,
  no_reacqs t ->
  no_reacq ad t.
Proof.
  unfold no_reacqs. trivial.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Corollary noreacqs_subst : forall x tx t,
  no_reacqs t ->
  no_reacqs tx ->
  no_reacqs <{[x := tx] t}>.
Proof.
  intros ** ?. auto using noreacq_subst.
Qed.


