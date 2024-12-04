From Elo Require Import Core.

From Elo Require Import ValidAddresses.
From Elo Require Import NoInit.
From Elo Require Import ValidBlocks.
From Elo Require Import InheritanceNoInit.

(* ------------------------------------------------------------------------- *)
(* one-init                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive one_init (ad : addr) : tm -> Prop :=
  | oneinit_call1    : forall t1 t2,   one_init ad t1 ->
                                       no_init  ad t2 ->
                                       one_init ad <{call t1 t2    }>
  | oneinit_call2    : forall t1 t2,   no_init  ad t1 ->
                                       one_init ad t2 ->
                                       one_init ad <{call t1 t2    }>
  | oneinit_new      : forall T t,     one_init ad t  ->
                                       one_init ad <{new t : T     }>
  | oneinit_init_eq  : forall t T,     no_init  ad t  ->
                                       one_init ad <{init ad  t : T}>
  | oneinit_init_neq : forall ad' t T, ad <> ad'      ->
                                       one_init ad t  ->
                                       one_init ad <{init ad' t : T}>
  | oneinit_load     : forall t,       one_init ad t  ->
                                       one_init ad <{*t            }>
  | oneinit_asg1     : forall t1 t2,   one_init ad t1 ->
                                       no_init  ad t2 ->
                                       one_init ad <{t1 := t2      }>
  | oneinit_asg2     : forall t1 t2,   no_init  ad t1 ->
                                       one_init ad t2 ->
                                       one_init ad <{t1 := t2      }>
  | oneinit_acq1     : forall t1 x t2, one_init ad t1 ->
                                       no_init  ad t2 ->
                                       one_init ad <{acq t1 x t2   }>
  | oneinit_acq2     : forall t1 x t2, no_init  ad t1 ->
                                       one_init ad t2 ->
                                       one_init ad <{acq t1 x t2   }>
  | oneinit_cr       : forall ad' t,   one_init ad t  ->
                                       one_init ad <{cr ad' t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _oneinit tt :=
  match goal with
  | H : one_init _ <{unit        }> |- _ => inv H
  | H : one_init _ <{nat _       }> |- _ => inv H
  | H : one_init _ <{var _       }> |- _ => inv H
  | H : one_init _ <{fn _ _ _    }> |- _ => inv H
  | H : one_init _ <{call _ _    }> |- _ => tt H
  | H : one_init _ <{&_ : _      }> |- _ => inv H
  | H : one_init _ <{new _ : _   }> |- _ => tt H
  | H : one_init _ <{init _ _ : _}> |- _ => tt H
  | H : one_init _ <{* _         }> |- _ => tt H
  | H : one_init _ <{_ := _      }> |- _ => tt H
  | H : one_init _ <{acq _ _ _   }> |- _ => tt H
  | H : one_init _ <{cr _ _      }> |- _ => tt H
  | H : one_init _ <{spawn _     }> |- _ => inv H
  end.

Ltac inv_oneinit  := _oneinit inv.
Ltac invc_oneinit := _oneinit invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma oneinit_ad_bound : forall ad m t,
  valid_addresses m t ->
  (* --- *)
  one_init ad t ->
  ad < #m.
Proof.
  intros. induction t; invc_vad; invc_oneinit; auto.
Qed.

Lemma noinit_oneinit_contradiction : forall ad t,
  no_init ad t ->
  one_init ad t ->
  False.
Proof.
  intros. induction t; invc_noinit; invc_oneinit; auto.
Qed.

Corollary noinits_oneinit_contradiction : forall ad t,
  no_inits t ->
  one_init ad t ->
  False.
Proof.
  eauto using noinit_oneinit_contradiction.
Qed.

Lemma noinit_to_oneinit : forall t1 t2 ad T,
  no_init ad t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  one_init ad t2.
Proof.
  intros. ind_tstep; invc_noinit; auto using one_init.
Qed.

Lemma oneinit_to_noinit : forall t1 t2 ad t,
  one_init ad t1 ->
  t1 --[e_insert ad t]--> t2 ->
  no_init ad t2.
Proof.
  intros. ind_tstep; invc_oneinit; auto using no_init;
  exfalso; eauto using noinit_insert_contradiction.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma oneinit_subst : forall ad x tx t,
  no_init  ad tx -> 
  one_init ad t  ->
  one_init ad <{[x := tx] t}>.
Proof.
  intros. induction t; simpl; try destruct _str_eq_dec;
  invc_oneinit; eauto using noinit_subst, one_init.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_oneinit_preservation L :=
  intros; ind_tstep; try invc_vb; repeat invc_oneinit;
  eauto using L, oneinit_subst, one_init;
  exfalso; eauto using noinits_from_value, noinits_oneinit_contradiction.

Lemma oneinit_preservation_none : forall ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_none]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_none. Qed.

Lemma oneinit_preservation_alloc : forall ad t1 t2 ad' T',
  ad <> ad' ->
  one_init ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_alloc. Qed.

Lemma oneinit_preservation_insert : forall ad t1 t2 ad' t',
  valid_blocks t1 ->
  (* --- *)
  ad <> ad' ->
  one_init ad t1 ->
  t1 --[e_insert ad' t']--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_insert. Qed.

Lemma oneinit_preservation_read : forall ad t1 t2 ad' t',
  no_inits t' ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_read. Qed.

Lemma oneinit_preservation_write : forall ad t1 t2 ad' t',
  valid_blocks t1 ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_write. Qed.

Lemma oneinit_preservation_acq : forall ad t1 t2 ad' t',
  no_inits t' ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_acq. Qed.

Lemma oneinit_preservation_rel : forall ad t1 t2 ad',
  one_init ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_rel. Qed.

Lemma oneinit_preservation_spawn : forall ad t1 t2 tid t,
  valid_blocks t1 ->
  (* --- *)
  one_init ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  one_init ad t2.
Proof. solve_oneinit_preservation noinit_preservation_spawn. Qed.

(* inheritance ------------------------------------------------------------- *)

Local Ltac solve_oneinit_inheritance L :=
  intros; ind_tstep; repeat invc_vb; try invc_oneinit;
  eauto using L, one_init; exfalso;
  eauto using noinit_from_value, noinit_subst, noinit_oneinit_contradiction.

Lemma oneinit_inheritance_none : forall ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  one_init ad t2 ->
  t1 --[e_none]--> t2 ->
  one_init ad t1.
Proof. solve_oneinit_inheritance noinit_inheritance_none. Qed.

Lemma oneinit_inheritance_alloc : forall ad t1 t2 ad' T',
  ad <> ad' ->
  one_init ad t2 ->
  t1 --[e_alloc ad' T']--> t2 ->
  one_init ad t1.
Proof. solve_oneinit_inheritance noinit_inheritance_alloc. Qed.

Lemma oneinit_inheritance_insert : forall ad t1 t2 ad' t',
  valid_blocks t1 ->
  (* --- *)
  ad <> ad' ->
  one_init ad t2 ->
  t1 --[e_insert ad' t']--> t2 ->
  one_init ad t1.
Proof. solve_oneinit_inheritance noinit_inheritance_insert. Qed.

Lemma oneinit_inheritance_read : forall ad t1 t2 ad' t',
  no_inits t' ->
  (* --- *)
  one_init ad t2 ->
  t1 --[e_read ad' t']--> t2 ->
  one_init ad t1.
Proof. solve_oneinit_inheritance noinit_inheritance_read. Qed.

Lemma oneinit_inheritance_write : forall ad t1 t2 ad' t',
  valid_blocks t1 ->
  (* --- *)
  one_init ad t2 ->
  t1 --[e_write ad' t']--> t2 ->
  one_init ad t1.
Proof. solve_oneinit_inheritance noinit_inheritance_write. Qed.

Lemma oneinit_inheritance_acq : forall ad t1 t2 ad' t',
  valid_blocks t1 ->
  no_inits t' ->
  (* --- *)
  one_init ad t2 ->
  t1 --[e_acq ad' t']--> t2 ->
  one_init ad t1.
Proof. solve_oneinit_inheritance noinit_inheritance_acq. Qed.

Lemma oneinit_inheritance_rel : forall ad t1 t2 ad',
  one_init ad t2 ->
  t1 --[e_rel ad']--> t2 ->
  one_init ad t1.
Proof. solve_oneinit_inheritance noinit_inheritance_rel. Qed.

Lemma oneinit_inheritance_spawn : forall ad t1 t2 tid t,
  valid_blocks t1 ->
  (* --- *)
  one_init ad t2 ->
  t1 --[e_spawn tid t]--> t2 ->
  one_init ad t1.
Proof. solve_oneinit_inheritance noinit_inheritance_spawn. Qed.

