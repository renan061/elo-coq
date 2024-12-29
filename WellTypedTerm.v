From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* well-typed-term                                                           *)
(* ------------------------------------------------------------------------- *)

Definition well_typed_term (t : tm) :=
  exists T, empty |-- t is T.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_wtt_inversion := 
  intros * [? ?]; repeat split;
  inv_typeof; try discriminate; eauto; eexists; eauto.

Local Lemma inv_wtt_seq : forall t1 t2,
  well_typed_term <{t1; t2}> ->
  well_typed_term t1 /\ well_typed_term t2.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_if : forall t1 t2 t3,
  well_typed_term <{if t1 then t2 else t3 end}> ->
  well_typed_term t1 /\ well_typed_term t2 /\ well_typed_term t3.
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

Local Lemma inv_wtt_ref : forall ad T,
  well_typed_term <{&ad : T}> ->
    (exists T', T = `r&T'`) \/
    (exists T', T = `x&T'`) \/
    (exists T', T = `w&T'`).
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_new : forall t T,
  well_typed_term <{new t : T}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_init : forall ad t T,
  well_typed_term <{init ad t : T}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_load : forall t,
  well_typed_term <{*t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_asg : forall t1 t2,
  well_typed_term <{t1 := t2}> ->
  well_typed_term t1 /\ well_typed_term t2.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_acq : forall t1 x t2,
  well_typed_term <{acq t1 x t2}> ->
  well_typed_term t1 /\
  (exists Tx T, empty |-- t1 is `x&Tx` /\ empty[x <== Tx] |-- t2 is T).
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_cr : forall ad t,
  well_typed_term <{cr ad t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Lemma inv_wtt_spawn : forall t,
  well_typed_term <{spawn t}> ->
  well_typed_term t.
Proof. solve_wtt_inversion. Qed.

Local Notation wtt := (well_typed_term).

Ltac invc_wtt :=
  match goal with
  | H : wtt <{unit        }> |- _ => clear H
  | H : wtt <{nat _       }> |- _ => clear H
  | H : wtt <{_; _        }> |- _ => eapply inv_wtt_seq   in H as [? ?]
  | H : wtt (tm_if _ _ _  )  |- _ => eapply inv_wtt_if    in H as [? [? ?]]
  | H : wtt <{var _       }> |- _ => eapply inv_wtt_var   in H; contradiction
  | H : wtt <{fn _ _ _    }> |- _ => eapply inv_wtt_fun   in H as [? ?]
  | H : wtt <{call _ _    }> |- _ => eapply inv_wtt_call  in H as [? ?]
  | H : wtt <{& _ : _     }> |- _ => eapply inv_wtt_ref   in H
                                                    as [[? ?] | [[? ?] | [? ?]]]
  | H : wtt <{new _ : _   }> |- _ => eapply inv_wtt_new   in H
  | H : wtt <{init _ _ : _}> |- _ => eapply inv_wtt_init  in H
  | H : wtt <{* _         }> |- _ => eapply inv_wtt_load  in H
  | H : wtt <{_ := _      }> |- _ => eapply inv_wtt_asg   in H as [? ?]
  | H : wtt <{acq _ _ _   }> |- _ => eapply inv_wtt_acq   in H as [? [? [? ?]]]
  | H : wtt <{cr _ _      }> |- _ => eapply inv_wtt_cr    in H
  | H : wtt <{spawn _     }> |- _ => eapply inv_wtt_spawn in H
  end.

(* ------------------------------------------------------------------------- *)
(* auxiliary lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma wtt_insert_term : forall t1 t2 ad t T,
  well_typed_term t1 ->
  t1 --[e_insert ad t T]--> t2 ->
  well_typed_term t.
Proof.
  intros. ind_tstep; invc_wtt; auto.
Qed.

Lemma wtt_write_term : forall t1 t2 ad t,
  well_typed_term t1 ->
  t1 --[e_write ad t]--> t2 ->
  well_typed_term t.
Proof.
  intros. ind_tstep; invc_wtt; auto.
Qed.

Lemma wtt_spawn_term : forall t1 t2 tid t,
  well_typed_term t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  well_typed_term t.
Proof.
  intros. ind_tstep; invc_wtt; auto.
Qed.

Lemma wtt_alloc_type : forall t1 t2 ad T,
  well_typed_term t1 ->
  (* --- *)
  t1 --[e_alloc ad T]--> t2 ->
  (exists T', T = `r&T'`) \/ (exists T', T = `x&T'`) \/ (exists T', T = `w&T'`).
Proof.
  intros * [T' ?] **. gendep T'. ind_tstep; intros; invc_typeof; eauto.
Qed.

Lemma wtt_insert_type : forall t1 t2 ad t T,
  well_typed_term t1 ->
  (* --- *)
  t1 --[e_insert ad t T]--> t2 ->
  (exists T', T = `r&T'`) \/ (exists T', T = `x&T'`) \/ (exists T', T = `w&T'`).
Proof.
  intros * [T' ?] **. gendep T'. ind_tstep; intros; invc_typeof; eauto.
Qed.

Lemma wtt_typeof_insert_term_R : forall t1 t2 ad t T,
  well_typed_term t1 ->
  t1 --[e_insert ad t `r&T`]--> t2 ->
  empty |-- t is `Safe T`.
Proof.
  intros * [T ?] **. gendep T. ind_tstep; intros; invc_typeof; eauto.
Qed.

Lemma wtt_typeof_insert_term_X : forall t1 t2 ad t T,
  well_typed_term t1 ->
  t1 --[e_insert ad t `x&T`]--> t2 ->
  empty |-- t is T.
Proof.
  intros * [T ?] **. gendep T. ind_tstep; intros; invc_typeof; eauto.
Qed.

Lemma wtt_typeof_insert_term_W : forall t1 t2 ad t T,
  well_typed_term t1 ->
  t1 --[e_insert ad t `w&T`]--> t2 ->
  empty |-- t is T.
Proof.
  intros * [T ?] **. gendep T. ind_tstep; intros; invc_typeof; eauto.
Qed.

