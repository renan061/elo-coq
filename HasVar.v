From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* has-var                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive has_var (x : id) : tm  -> Prop :=
  | hasvar_plus1  : forall t1 t2,    has_var x t1 ->
                                     has_var x <{t1 + t2                  }>
  | hasvar_plus2  : forall t1 t2,    has_var x t2 ->
                                     has_var x <{t1 + t2                  }>
  | hasvar_monus1 : forall t1 t2,    has_var x t1 ->
                                     has_var x <{t1 - t2                  }>
  | hasvar_monus2 : forall t1 t2,    has_var x t2 ->
                                     has_var x <{t1 - t2                  }>
  | hasvar_seq1   : forall t1 t2,    has_var x t1 ->
                                     has_var x <{t1; t2                   }>
  | hasvar_seq2   : forall t1 t2,    has_var x t2 ->
                                     has_var x <{t1; t2                   }>
  | hasvar_if1    : forall t1 t2 t3, has_var x t1 ->
                                     has_var x <{if t1 then t2 else t3 end}>
  | hasvar_if2    : forall t1 t2 t3, has_var x t2 ->
                                     has_var x <{if t1 then t2 else t3 end}>
  | hasvar_if3    : forall t1 t2 t3, has_var x t3 ->
                                     has_var x <{if t1 then t2 else t3 end}>
  | hasvar_while1 : forall t1 t2,    has_var x t1 ->
                                     has_var x <{while t1 do t2 end       }>
  | hasvar_while2 : forall t1 t2,    has_var x t2 ->
                                     has_var x <{while t1 do t2 end       }>
  | hasvar_var    :                  has_var x <{var x                    }>
  | hasvar_fun    : forall x' Tx t,  x <> x'      ->
                                     has_var x t  ->
                                     has_var x <{fn x' Tx t               }>
  | hasvar_call1  : forall t1 t2,    has_var x t1 ->
                                     has_var x <{call t1 t2               }>
  | hasvar_call2  : forall t1 t2,    has_var x t2 ->
                                     has_var x <{call t1 t2               }>
  | hasvar_new    : forall t T,      has_var x t  ->
                                     has_var x <{new t : T                }>
  | hasvar_init   : forall ad t T,   has_var x t  ->
                                     has_var x <{init ad t : T            }>
  | hasvar_load   : forall t,        has_var x t  ->
                                     has_var x <{*t                       }>
  | hasvar_asg1   : forall t1 t2,    has_var x t1 ->
                                     has_var x <{t1 := t2                 }>
  | hasvar_asg2   : forall t1 t2,    has_var x t2 ->
                                     has_var x <{t1 := t2                 }>
  | hasvar_acq1   : forall t1 x' t2, has_var x t1 ->
                                     has_var x <{acq t1 x' t2             }>
  | hasvar_acq2   : forall t1 x' t2, x <> x'      ->
                                     x <> SELF    ->
                                     has_var x t2 ->
                                     has_var x <{acq t1 x' t2             }>
  | hasvar_cr     : forall ad t,     has_var x t  ->
                                     has_var x <{cr ad t                  }>
  | hasvar_wait   : forall t,        has_var x t  ->
                                     has_var x <{wait t                   }>
  | hasvar_spawn  : forall t,        has_var x t  ->
                                     has_var x <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _hasvar tt :=
  match goal with
  | H : has_var _  <{unit                  }> |- _ => invc H
  | H : has_var _  <{nat _                 }> |- _ => invc H
  | H : has_var _  <{_ + _                 }> |- _ => tt H
  | H : has_var _  <{_ - _                 }> |- _ => tt H
  | H : has_var _  <{_; _                  }> |- _ => tt H
  | H : has_var _  <{if _ then _ else _ end}> |- _ => tt H
  | H : has_var _  <{while _ do _ end      }> |- _ => tt H
  | H : has_var ?x <{var ?x                }> |- _ => clear H
  | H : has_var _  <{var _                 }> |- _ => tt H
  | H : has_var _  <{fn _ _ _              }> |- _ => tt H
  | H : has_var _  <{call _ _              }> |- _ => tt H
  | H : has_var _  <{&_ : _                }> |- _ => invc H
  | H : has_var _  <{new _ : _             }> |- _ => tt H
  | H : has_var _  <{init _ _ : _          }> |- _ => tt H
  | H : has_var _  <{* _                   }> |- _ => tt H
  | H : has_var _  <{_ := _                }> |- _ => tt H
  | H : has_var _  <{acq _ _ _             }> |- _ => tt H
  | H : has_var _  <{cr _ _                }> |- _ => tt H
  | H : has_var _  <{wait _                }> |- _ => tt H
  | H : has_var _  <{reacq _               }> |- _ => invc H
  | H : has_var _  <{spawn _               }> |- _ => tt H
  end.

Ltac inv_hasvar  := _hasvar inv.
Ltac invc_hasvar := _hasvar invc.

(* decidability ------------------------------------------------------------ *)

Corollary hasvar_dec : forall x t,
  Decidable.decidable (has_var x t).
Proof.
  unfold Decidable.decidable. intros. induction t;
  try (destruct IHt1, IHt2, IHt3 || destruct IHt1, IHt2 || destruct IHt);
  try match goal with x1: id, x2: id |- _ => str_eq_dec x1 x2 end;
  try str_eq_dec SELF x; auto using has_var;
  right; intros ?; invc_hasvar; auto.
Qed.

(* lemmas ------------------------------------------------------------------ *)

Lemma hasvar_subst : forall x t tx,
  ~ (has_var x t) ->
  t = <{[x := tx] t}>.
Proof.
  intros * Hnhv **. induction t; simpl; trivial;
  repeat destruct _str_eq_dec; subst; trivial;
  try (rewrite <- IHt;  auto using has_var);
  try (rewrite <- IHt1; auto using has_var);
  try (rewrite <- IHt2; auto using has_var);
  try (rewrite <- IHt3; auto using has_var).
  exfalso. auto using has_var.
Qed.

Lemma hasvar_type_contradiction : forall Gamma x t T,
  Gamma |-- t is T ->
  Gamma x = None   ->
  has_var x t      ->
  False.
Proof.
  intros. ind_typeof; inv_hasvar; auto using ctx_eqv_safe_lookup;
  repeat (rewrite lookup_update_neq in *; auto using ctx_eqv_safe_lookup).
Qed.

Lemma safe_refW_subst1 : forall Gamma x tx t Tx T T',
  Tx = `w&T'`                     ->
  empty |-- tx is Tx              ->
  safe Gamma[x <== Tx] |-- t is T ->
  <{[x := tx] t}> = t.
Proof.
  intros. subst. destruct (hasvar_dec x t).
  - exfalso.
    eauto using safe_refW_lookup_update_eq_none, hasvar_type_contradiction.
  - erewrite hasvar_subst; trivial.
Qed.

Lemma safe_refW_subst2 : forall Gamma x y tx t Tx Ts Ty T T',
  x <> y                                                   ->
  x <> SELF                                                ->
  Tx = `w&T'`                                              ->
  empty |-- tx is Tx                                       ->
  (safe Gamma[x <== Tx])[SELF <== Ts][y <== Ty] |-- t is T ->
  <{[x := tx] t}> = t.
Proof.
  intros. subst. destruct (hasvar_dec x t).
  - exfalso.
    eapply hasvar_type_contradiction. 3: eauto. 1: eauto.
    do 2 (rewrite lookup_update_neq; auto).
    auto using safe_refW_lookup_update_eq_none.
  - erewrite hasvar_subst; trivial.
Qed.

Lemma safe_fun_subst1 : forall Gamma x tx t Tx T T1 T2,
  Tx = `T1 --> T2`                ->
  empty |-- tx is Tx              ->
  safe Gamma[x <== Tx] |-- t is T ->
  <{[x := tx] t}> = t.
Proof.
  intros. subst. destruct (hasvar_dec x t).
  - exfalso.
    eauto using safe_fun_lookup_update_eq_none, hasvar_type_contradiction.
  - erewrite hasvar_subst; trivial.
Qed.

Lemma safe_fun_subst2 : forall Gamma x y tx t Tx Ts Ty T T1 T2,
  x <> y                                                   ->
  x <> SELF                                                ->
  Tx = `T1 --> T2`                                         ->
  empty |-- tx is Tx                                       ->
  (safe Gamma[x <== Tx])[SELF <== Ts][y <== Ty] |-- t is T ->
  <{[x := tx] t}> = t.
Proof.
  intros. subst. destruct (hasvar_dec x t).
  - exfalso.
    eapply hasvar_type_contradiction. 3: eauto. 1: eauto.
    do 2 (rewrite lookup_update_neq; auto).
    auto using safe_fun_lookup_update_eq_none.
  - erewrite hasvar_subst; trivial.
Qed.

