From Elo Require Import Core.

From Elo Require Import Properties2.

(* ------------------------------------------------------------------------- *)
(* has-ref                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive has_ref (ad : addr) : tm -> Prop :=
  | hasref_fun   : forall x Tx t,  has_ref ad t  ->
                                   has_ref ad <{fn x Tx t     }>
  | hasref_call1 : forall t1 t2,   has_ref ad t1 ->
                                   has_ref ad <{call t1 t2    }>
  | hasref_call2 : forall t1 t2,   has_ref ad t2 ->
                                   has_ref ad <{call t1 t2    }>
  | hasref_ref   : forall T,       has_ref ad <{&ad : T       }>
  | hasref_new   : forall t T,     has_ref ad t  ->
                                   has_ref ad <{new t : T     }>
  | hasref_init  : forall ad' t T, has_ref ad t  ->
                                   has_ref ad <{init ad' t : T}>
  | hasref_load  : forall t,       has_ref ad t  ->
                                   has_ref ad <{*t            }>
  | hasref_asg1  : forall t1 t2,   has_ref ad t1 ->
                                   has_ref ad <{t1 := t2      }>
  | hasref_asg2  : forall t1 t2,   has_ref ad t2 ->
                                   has_ref ad <{t1 := t2      }>
  | hasref_acq1  : forall t1 t2,   has_ref ad t1 ->
                                   has_ref ad <{acq t1 t2     }>
  | hasref_acq2  : forall t1 t2,   has_ref ad t2 ->
                                   has_ref ad <{acq t1 t2     }>
  | hasref_cr    : forall ad' t,   has_ref ad t  ->
                                   has_ref ad <{cr ad' t      }>
  | hasref_spawn : forall t,       has_ref ad t ->
                                   has_ref ad <{spawn t       }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _hasref tt :=
  match goal with
  | H : has_ref _ <{unit        }> |- _ => invc H
  | H : has_ref _ <{nat _       }> |- _ => invc H
  | H : has_ref _ <{var _       }> |- _ => invc H
  | H : has_ref _ <{fn _ _ _    }> |- _ => tt H
  | H : has_ref _ <{call _ _    }> |- _ => tt H
  | H : has_ref _ <{&_ : _      }> |- _ => tt H
  | H : has_ref _ <{new _ : _   }> |- _ => tt H
  | H : has_ref _ <{init _ _ : _}> |- _ => tt H
  | H : has_ref _ <{* _         }> |- _ => tt H
  | H : has_ref _ <{_ := _      }> |- _ => tt H
  | H : has_ref _ <{acq _ _     }> |- _ => tt H
  | H : has_ref _ <{cr _ _      }> |- _ => tt H
  | H : has_ref _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_hasref  := _hasref inv.
Ltac invc_hasref := _hasref invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma noref_hasref_contradiction : forall ad t,
  no_ref ad t ->
  has_ref ad t ->
  False.
Proof.
  intros. induction t; invc_noref; invc_hasref; auto.
Qed.

Lemma hasref_from_write : forall ad t t1 t2,
  t1 --[e_write ad t]--> t2 ->
  has_ref ad t1.
Proof.
  intros. ind_tstep; eauto using has_ref.
Qed.

Lemma hasref_insert_term : forall m t1 t2 ad t,
  has_ref m t ->
  t1 --[e_insert ad t]--> t2 ->
  has_ref m t1.
Proof.
  intros. ind_tstep; eauto using has_ref.
Qed.

Lemma hasref_write_term : forall m t1 t2 ad t,
  has_ref m t ->
  t1 --[e_write ad t]--> t2 ->
  has_ref m t1.
Proof.
  intros. ind_tstep; eauto using has_ref.
Qed.

