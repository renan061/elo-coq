From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* has-var                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive has_var (x : id) : tm  -> Prop :=
  | hasvar_seq1  : forall t1 t2,    has_var x t1 ->
                                    has_var x <{t1; t2       }>
  | hasvar_seq2  : forall t1 t2,    has_var x t2 ->
                                    has_var x <{t1; t2       }>
  | hasvar_var   :                  has_var x <{var x        }>
  | hasvar_fun   : forall x' Tx t,  x <> x'      ->
                                    has_var x t  ->
                                    has_var x <{fn x' Tx t   }>
  | hasvar_call1 : forall t1 t2,    has_var x t1 ->
                                    has_var x <{call t1 t2   }>
  | hasvar_call2 : forall t1 t2,    has_var x t2 ->
                                    has_var x <{call t1 t2   }>
  | hasvar_new   : forall t T,      has_var x t  ->
                                    has_var x <{new t : T    }>
  | hasvar_init  : forall ad t T,   has_var x t  ->
                                    has_var x <{init ad t : T}>
  | hasvar_load  : forall t,        has_var x t  ->
                                    has_var x <{*t           }>
  | hasvar_asg1  : forall t1 t2,    has_var x t1 ->
                                    has_var x <{t1 := t2     }>
  | hasvar_asg2  : forall t1 t2,    has_var x t2 ->
                                    has_var x <{t1 := t2     }>
  | hasvar_acq1  : forall t1 x' t2, has_var x t1 ->
                                    has_var x <{acq t1 x' t2 }>
  | hasvar_acq2  : forall t1 x' t2, x <> x'      ->
                                    has_var x t2 ->
                                    has_var x <{acq t1 x' t2 }>
  | hasvar_cr    : forall ad t,     has_var x t  ->
                                    has_var x <{cr ad t      }>
  | hasvar_spawn : forall t,        has_var x t  ->
                                    has_var x <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _hasvar tt :=
  match goal with
  | H : has_var _  <{unit          }> |- _ => invc H
  | H : has_var _  <{nat _         }> |- _ => invc H
  | H : has_var _  <{_; _          }> |- _ => tt H
  | H : has_var ?x <{var ?x        }> |- _ => clear H
  | H : has_var _  <{var _         }> |- _ => tt H
  | H : has_var _  <{fn _ _ _      }> |- _ => tt H
  | H : has_var _  <{call _ _      }> |- _ => tt H
  | H : has_var _  <{&_ : _        }> |- _ => invc H
  | H : has_var _  <{new _ : _     }> |- _ => tt H
  | H : has_var _  <{init _ _ : _  }> |- _ => tt H
  | H : has_var _  <{* _           }> |- _ => tt H
  | H : has_var _  <{_ := _        }> |- _ => tt H
  | H : has_var _  <{acq _ _ _     }> |- _ => tt H
  | H : has_var _  <{cr _ _        }> |- _ => tt H
  | H : has_var _  <{spawn _       }> |- _ => tt H
  end.

Ltac inv_hasvar  := _hasvar inv.
Ltac invc_hasvar := _hasvar invc.

(* decidability ------------------------------------------------------------ *)

Corollary hasvar_dec : forall x t,
  Decidable.decidable (has_var x t).
Proof.
  unfold Decidable.decidable. intros. induction t;
  try (destruct IHt || destruct IHt1, IHt2);
  try match goal with x1: id, x2: id |- _ => str_eq_dec x1 x2 end;
  auto using has_var;
  right; intros ?; invc_hasvar; auto.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma hasvar_subst : forall x t tx,
  ~ (has_var x t) ->
  t = <{[x := tx] t}>.
Proof.
  intros * Hnhv **. induction t; simpl; trivial;
  try destruct _str_eq_dec; subst; trivial;
  solve [ rewrite <- IHt; auto using has_var
        | rewrite <- IHt1; try rewrite <- IHt2; auto using has_var
        | exfalso; auto using has_var
        ].
Qed.

Lemma hasvar_type_contradiction : forall Gamma x t T,
  Gamma |-- t is T ->
  Gamma x = None ->
  has_var x t ->
  False.
Proof.
  intros. ind_typeof; invc_hasvar; auto using ctx_eqv_safe_lookup.
  - rewrite lookup_update_neq in IHtype_of; auto.
  - rewrite lookup_update_neq in IHtype_of2; auto using ctx_eqv_safe_lookup.
Qed.

Lemma safe_refW_subst1 : forall Gamma x tx t Tx T T',
  Tx = `w&T'` ->
  empty |-- tx is Tx ->
  safe Gamma[x <== Tx] |-- t is T ->
  <{[x := tx] t}> = t.
Proof.
  intros. subst. destruct (hasvar_dec x t).
  - exfalso.
    eauto using safe_refW_lookup_update_eq_none, hasvar_type_contradiction.
  - erewrite hasvar_subst; trivial.
Qed.

Lemma safe_refW_subst2 : forall Gamma x y tx t Tx Ty T T',
  x <> y ->
  Tx = `w&T'` ->
  empty |-- tx is Tx ->
  (safe Gamma[x <== Tx])[y <== Ty] |-- t is T ->
  <{[x := tx] t}> = t.
Proof.
  intros. subst. destruct (hasvar_dec x t).
  - exfalso.
    eapply hasvar_type_contradiction. 3: eauto. 1: eauto.
    rewrite lookup_update_neq; auto using safe_refW_lookup_update_eq_none.
  - erewrite hasvar_subst; trivial.
Qed.

Lemma safe_fun_subst1 : forall Gamma x tx t Tx T T1 T2,
  Tx = `T1 --> T2` ->
  empty |-- tx is Tx ->
  safe Gamma[x <== Tx] |-- t is T ->
  <{[x := tx] t}> = t.
Proof.
  intros. subst. destruct (hasvar_dec x t).
  - exfalso.
    eauto using safe_fun_lookup_update_eq_none, hasvar_type_contradiction.
  - erewrite hasvar_subst; trivial.
Qed.

Lemma safe_fun_subst2 : forall Gamma x y tx t Tx Ty T T1 T2,
  x <> y ->
  Tx = `T1 --> T2` ->
  empty |-- tx is Tx ->
  (safe Gamma[x <== Tx])[y <== Ty] |-- t is T ->
  <{[x := tx] t}> = t.
Proof.
  intros. subst. destruct (hasvar_dec x t).
  - exfalso.
    eapply hasvar_type_contradiction. 3: eauto. 1: eauto.
    rewrite lookup_update_neq; auto using safe_fun_lookup_update_eq_none.
  - erewrite hasvar_subst; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* not-has-var                                                               *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_cons_nhv := 
  intros ** ?; invc_hasvar; eauto.

Lemma nhv_unit : forall x,
  ~ has_var x <{unit}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_nat : forall x n,
  ~ has_var x <{nat n}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_seq : forall x t1 t2,
  ~ has_var x t1 -> ~ has_var x t2 -> ~ has_var x <{t1; t2}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_var : forall x x',
  x <> x' -> ~ has_var x <{var x'}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_fun : forall x x' Tx t,
  ~ has_var x t -> ~ has_var x <{fn x' Tx t}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_call : forall x t1 t2,
  ~ has_var x t1 -> ~ has_var x t2 -> ~ has_var x <{call t1 t2}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_ref : forall x ad T,
  ~ has_var x <{&ad : T}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_new : forall x t T,
  ~ has_var x t -> ~ has_var x <{new t : T}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_init : forall x ad t T,
  ~ has_var x t -> ~ has_var x <{init ad t : T}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_load : forall x t,
  ~ has_var x t -> ~ has_var x <{*t}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_asg : forall x t1 t2,
  ~ has_var x t1 -> ~ has_var x t2 -> ~ has_var x <{t1 := t2}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_acq : forall x x' t1 t2,
  ~ has_var x t1 -> ~ has_var x t2 -> ~ has_var x <{acq t1 x' t2}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_cr : forall x ad t,
  ~ has_var x t -> ~ has_var x <{cr ad t}>.
Proof. solve_cons_nhv. Qed.

Lemma nhv_spawn : forall x t,
  ~ has_var x t -> ~ has_var x <{spawn t}>.
Proof. solve_cons_nhv. Qed.

#[export] Hint Resolve
  nhv_unit  nhv_nat
  nhv_seq
  nhv_var   nhv_fun   nhv_call
  nhv_ref   nhv_new   nhv_init nhv_load  nhv_asg
  nhv_acq   nhv_cr
  nhv_spawn
  : not_has_var.

(* inversion --------------------------------------------------------------- *)

Local Lemma inv_nhv_seq : forall x t1 t2,
  ~ has_var x <{t1; t2}> ->
  ~ has_var x t1 /\ ~ has_var x t2.
Proof. intros. split; eauto using has_var. Qed.

Local Lemma inv_nhv_var : forall x x',
  ~ has_var x <{var x'}> ->
  x <> x'.
Proof. intros. str_eq_dec x' x; eauto using has_var. Qed.

Local Lemma inv_nhv_fun : forall x x' Tx t,
  ~ has_var x <{fn x' Tx t}> ->
  (x = x') \/ (x <> x' /\ ~ has_var x t).
Proof. intros. str_eq_dec x x'; eauto 6 using has_var. Qed.

Local Lemma inv_nhv_call : forall x t1 t2,
  ~ has_var x <{call t1 t2}> ->
  ~ has_var x t1 /\ ~ has_var x t2.
Proof. intros. split; eauto using has_var. Qed.

Local Lemma inv_nhv_new : forall x t T,
  ~ has_var x <{new t : T}> ->
  ~ has_var x t.
Proof. eauto using has_var. Qed.

Local Lemma inv_nhv_init : forall x ad t T,
  ~ has_var x <{init ad t : T}> ->
  ~ has_var x t.
Proof. eauto using has_var. Qed.

Local Lemma inv_nhv_load : forall x t,
  ~ has_var x <{*t}> ->
  ~ has_var x t.
Proof. eauto using has_var. Qed.

Local Lemma inv_nhv_asg : forall x t1 t2,
  ~ has_var x <{t1 := t2}> ->
  ~ has_var x t1 /\ ~ has_var x t2.
Proof. intros. split; eauto using has_var. Qed.

Local Lemma inv_nhv_acq : forall x t1 x' t2,
  ~ has_var x <{acq t1 x' t2}> ->
  ~ has_var x t1 /\ (x = x' \/ (x <> x' /\ ~ has_var x t2)).
Proof.
  intros. str_eq_dec x' x; split; eauto 6 using has_var.
Qed.

Local Lemma inv_nhv_cr : forall x ad t,
  ~ has_var x <{cr ad t}> ->
  ~ has_var x t.
Proof. eauto using has_var. Qed.

Local Lemma inv_nhv_spawn : forall x t,
  ~ has_var x <{spawn t}> ->
  ~ has_var x t.
Proof. eauto using has_var. Qed.

Ltac invc_nhv :=
  match goal with
  | H : ~ has_var _ <{unit        }> |- _ => clear H
  | H : ~ has_var _ <{nat _       }> |- _ => clear H
  | H : ~ has_var _ <{_; _        }> |- _ => eapply inv_nhv_seq   in H as [? ?]
  | H : ~ has_var _ <{var _       }> |- _ => eapply inv_nhv_var   in H; auto
  | H : ~ has_var _ <{fn _ _ _    }> |- _ => eapply inv_nhv_fun   in H
                                             as [? | [? ?]]; subst
  | H : ~ has_var _ <{call _ _    }> |- _ => eapply inv_nhv_call  in H as [? ?]
  | H : ~ has_var _ <{& _ : _     }> |- _ => clear H
  | H : ~ has_var _ <{new _ : _   }> |- _ => eapply inv_nhv_new   in H
  | H : ~ has_var _ <{init _ _ : _}> |- _ => eapply inv_nhv_init  in H
  | H : ~ has_var _ <{* _         }> |- _ => eapply inv_nhv_load  in H
  | H : ~ has_var _ <{_ := _      }> |- _ => eapply inv_nhv_asg   in H as [? ?]
  | H : ~ has_var _ <{acq _ _ _   }> |- _ => eapply inv_nhv_acq   in H
                                             as [? [? | [? ?]]]; subst
  | H : ~ has_var _ <{cr _ _      }> |- _ => eapply inv_nhv_acq   in H
  | H : ~ has_var _ <{spawn _     }> |- _ => eapply inv_nhv_spawn in H
  end.

