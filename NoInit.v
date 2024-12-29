From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-init                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive no_init (ad : addr) : tm -> Prop :=
  | noinit_unit  :                  no_init ad <{unit                     }>
  | noinit_nat   : forall n,        no_init ad <{nat n                    }>
  | noinit_seq   : forall t1 t2,    no_init ad t1 ->
                                    no_init ad t2 ->
                                    no_init ad <{t1; t2                   }>
  | noinit_if    : forall t1 t2 t3, no_init ad t1 ->
                                    no_init ad t2 ->
                                    no_init ad t3 ->
                                    no_init ad <{if t1 then t2 else t3 end}>
  | noinit_var   : forall x,        no_init ad <{var x                    }>
  | noinit_fun   : forall x Tx t,   no_init ad t  ->
                                    no_init ad <{fn x Tx t                }>
  | noinit_call  : forall t1 t2,    no_init ad t1 ->
                                    no_init ad t2 ->
                                    no_init ad <{call t1 t2               }>
  | noinit_ref   : forall ad' T,    no_init ad <{&ad' : T                 }>
  | noinit_new   : forall T t,      no_init ad t  ->
                                    no_init ad <{new t : T                }>
  | noinit_init  : forall ad' T t,  ad <> ad'     ->
                                    no_init ad t  ->
                                    no_init ad <{init ad' t : T           }>
  | noinit_load  : forall t,        no_init ad t  ->
                                    no_init ad <{*t                       }>
  | noinit_asg   : forall t1 t2,    no_init ad t1 ->
                                    no_init ad t2 ->
                                    no_init ad <{t1 := t2                 }>
  | noinit_acq   : forall t1 x t2,  no_init ad t1 ->
                                    no_init ad t2 ->
                                    no_init ad <{acq t1 x t2              }>
  | noinit_cr    : forall ad' t,    no_init ad t  ->
                                    no_init ad <{cr ad' t                 }>
  | noinit_spawn : forall t,        no_init ad t  ->
                                    no_init ad <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _noinit tt :=
  match goal with
  | H : no_init _   <{unit          }> |- _ => clear H
  | H : no_init _   <{nat _         }> |- _ => clear H
  | H : no_init _   <{_; _          }> |- _ => tt H
  | H : no_init _   (tm_if _ _ _    )  |- _ => tt H
  | H : no_init _   <{var _         }> |- _ => clear H
  | H : no_init _   <{fn _ _ _      }> |- _ => tt H
  | H : no_init _   <{call _ _      }> |- _ => tt H
  | H : no_init _   <{&_ : _        }> |- _ => clear H
  | H : no_init _   <{new _ : _     }> |- _ => tt H
  | H : no_init ?ad <{init ?ad _ : _}> |- _ => invc H; auto
  | H : no_init _   <{init _ _ : _  }> |- _ => tt H
  | H : no_init _   <{* _           }> |- _ => tt H
  | H : no_init _   <{_ := _        }> |- _ => tt H
  | H : no_init _   <{acq _ _ _     }> |- _ => tt H
  | H : no_init _   <{cr _ _        }> |- _ => tt H
  | H : no_init _   <{spawn _       }> |- _ => tt H
  end.

Ltac inv_noinit  := _noinit inv.
Ltac invc_noinit := _noinit invc.

(* decidability ------------------------------------------------------------ *)

Lemma noinit_dec : forall ad t,
  Decidable.decidable (no_init ad t).
Proof.
  unfold Decidable.decidable. unfold not. intros.
  induction t; auto using no_init;
  (destruct IHt1, IHt2, IHt3 || destruct IHt1, IHt2 || destruct IHt);
  auto using no_init;
  try solve [right; intros; invc_noinit; auto].
  match goal with ad1 : addr, ad2 : addr |- _ => nat_eq_dec ad1 ad2 end;
  auto using no_init.
  right. intros. invc_noinit.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma noinit_insert_term : forall ad t1 t2 ad' t' T',
  no_init ad t1 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  no_init ad t'.
Proof.
  intros. ind_tstep; invc_noinit; auto using no_init.
Qed.

Lemma noinit_write_term : forall ad t1 t2 ad' t',
  no_init ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  no_init ad t'.
Proof.
  intros. ind_tstep; invc_noinit; auto using no_init.
Qed.

Lemma noinit_insert_contradiction : forall t1 t2 ad t T,
  no_init ad t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_noinit; auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma noinit_subst : forall ad x tx t,
  no_init ad t ->
  no_init ad tx ->
  no_init ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_noinit;
  simpl in *; try destruct _str_eq_dec; auto using no_init.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_noinit_preservation :=
  intros; ind_tstep; repeat invc_noinit; auto using noinit_subst, no_init.

Lemma noinit_preservation_none : forall ad t1 t2,
  no_init ad t1 ->
  t1 --[e_none]--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_alloc : forall ad t1 t2 ad' T',
  ad <> ad' ->
  no_init ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_insert : forall ad t1 t2 ad' t' T',
  ad <> ad' ->
  no_init ad t1 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_read : forall ad t1 t2 ad' t',
  no_init ad t' ->
  (* --- *)
  no_init ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_write : forall ad t1 t2 ad' t',
  no_init ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_acq : forall ad t1 t2 ad' t',
  no_init ad t' ->
  (* --- *)
  no_init ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_rel : forall ad t1 t2 ad',
  no_init ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_spawn : forall ad t1 t2 tid' t',
  no_init ad t1 ->
  t1 --[e_spawn tid' t']--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_spawned : forall ad t1 t2 tid' t',
  no_init ad t1 ->
  t1 --[e_spawn tid' t']--> t2 ->
  no_init ad t'.
Proof. solve_noinit_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* no-inits                                                                  *)
(* ------------------------------------------------------------------------- *)

Definition no_inits (t : tm) := forall ad, no_init ad t.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_noinits :=
  unfold no_inits; intros; repeat split; intros; spec; invc_noinit; auto.

Local Lemma inv_noinits_seq : forall t1 t2,
  no_inits <{t1; t2}> -> no_inits t1 /\ no_inits t2.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_if : forall t1 t2 t3,
  no_inits (tm_if t1 t2 t3) -> no_inits t1 /\ no_inits t2 /\ no_inits t3.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_fun : forall x Tx t,
  no_inits <{fn x Tx t}> -> no_inits t.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_call : forall t1 t2,
  no_inits <{call t1 t2}> -> no_inits t1 /\ no_inits t2.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_new : forall t T,
  no_inits <{new t : T}> -> no_inits t.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_init : forall ad t T,
  no_inits <{init ad t : T}> -> False.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_load : forall t,
  no_inits <{*t}> -> no_inits t.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_asg : forall t1 t2,
  no_inits <{t1 := t2}> -> no_inits t1 /\ no_inits t2.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_acq : forall t1 x t2,
  no_inits <{acq t1 x t2}> -> no_inits t1 /\ no_inits t2.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_cr : forall ad t,
  no_inits <{cr ad t}> -> no_inits t.
Proof. solve_inv_noinits. Qed.

Local Lemma inv_noinits_spawn : forall t,
  no_inits <{spawn t}> -> no_inits t.
Proof. solve_inv_noinits. Qed.

Ltac invc_noinits :=
match goal with
| H : no_inits <{unit        }> |- _ => clear H
| H : no_inits <{nat _       }> |- _ => clear H
| H : no_inits <{_; _        }> |- _ => eapply inv_noinits_seq in H as [? ?]
| H : no_inits (tm_if _ _ _  )  |- _ => eapply inv_noinits_if  in H as [? [? ?]]
| H : no_inits <{var _       }> |- _ => clear H
| H : no_inits <{fn _ _ _    }> |- _ => eapply inv_noinits_fun   in H
| H : no_inits <{call _ _    }> |- _ => eapply inv_noinits_call  in H as [? ?]
| H : no_inits <{& _ : _     }> |- _ => clear H
| H : no_inits <{new _ : _   }> |- _ => eapply inv_noinits_new   in H
| H : no_inits <{init _ _ : _}> |- _ => eapply inv_noinits_init  in H; auto
| H : no_inits <{* _         }> |- _ => eapply inv_noinits_load  in H
| H : no_inits <{_ := _      }> |- _ => eapply inv_noinits_asg   in H as [? ?]
| H : no_inits <{acq _ _ _   }> |- _ => eapply inv_noinits_acq   in H as [? ?]
| H : no_inits <{cr _ _      }> |- _ => eapply inv_noinits_cr    in H
| H : no_inits <{spawn _     }> |- _ => eapply inv_noinits_spawn in H
end.

(* lemmas ------------------------------------------------------------------ *)

Corollary noinit_from_noinits : forall ad t,
  no_inits t ->
  no_init ad t.
Proof.
  unfold no_inits. auto.
Qed.

Corollary noinits_insert_term : forall t1 t2 ad' t' T',
  no_inits t1 ->
  t1 --[e_insert ad' t' T']--> t2 ->
  no_inits t'.
Proof.
  unfold no_inits. eauto using noinit_insert_term.
Qed.

Corollary noinits_write_term : forall t1 t2 ad' t',
  no_inits t1 ->
  t1 --[e_write ad' t']--> t2 ->
  no_inits t'.
Proof.
  unfold no_inits. eauto using noinit_write_term.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Corollary noinits_subst : forall x tx t,
  no_inits t ->
  no_inits tx ->
  no_inits <{[x := tx] t}>.
Proof.
  intros ** ?. auto using noinit_subst.
Qed.

