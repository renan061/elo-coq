From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-ref                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive no_ref (ad : addr) : tm -> Prop :=
  | noref_unit  :                 no_ref ad <{unit          }>
  | noref_nat   : forall n,       no_ref ad <{nat n         }>
  | noref_var   : forall x,       no_ref ad <{var x         }>
  | noref_fun   : forall x Tx t,  no_ref ad t  ->
                                  no_ref ad <{fn x Tx t     }>
  | noref_call  : forall t1 t2,   no_ref ad t1 ->
                                  no_ref ad t2 ->
                                  no_ref ad <{call t1 t2    }>
  | noref_ref   : forall ad' T,   ad <> ad'    ->
                                  no_ref ad <{&ad' : T      }>
  | noref_new   : forall t T,     no_ref ad t  ->
                                  no_ref ad <{new t : T     }>
  | noref_init  : forall ad' t T, no_ref ad t  ->
                                  no_ref ad <{init ad' t : T}>
  | noref_load  : forall t,       no_ref ad t  ->
                                  no_ref ad <{*t            }>
  | noref_asg   : forall t1 t2,   no_ref ad t1 ->
                                  no_ref ad t2 ->
                                  no_ref ad <{t1 := t2      }>
  | noref_acq   : forall t1 t2,   no_ref ad t1 ->
                                  no_ref ad t2 ->
                                  no_ref ad <{acq t1 t2     }>
  | noref_cr    : forall ad' t,   no_ref ad t  ->
                                  no_ref ad <{cr ad' t      }>
  | noref_spawn : forall t,       no_ref ad t ->
                                  no_ref ad <{spawn t       }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _noref tt :=
  match goal with
  | H : no_ref _   <{unit        }> |- _ => clear H
  | H : no_ref _   <{nat _       }> |- _ => clear H
  | H : no_ref _   <{var _       }> |- _ => clear H
  | H : no_ref _   <{fn _ _ _    }> |- _ => tt H
  | H : no_ref _   <{call _ _    }> |- _ => tt H
  | H : no_ref ?ad <{& ?ad : _   }> |- _ => invc H; eauto
  | H : no_ref _   <{&_ : _      }> |- _ => tt H
  | H : no_ref _   <{new _ : _   }> |- _ => tt H
  | H : no_ref _   <{init _ _ : _}> |- _ => tt H
  | H : no_ref _   <{* _         }> |- _ => tt H
  | H : no_ref _   <{_ := _      }> |- _ => tt H
  | H : no_ref _   <{acq _ _     }> |- _ => tt H
  | H : no_ref _   <{cr _ _      }> |- _ => tt H
  | H : no_ref _   <{spawn _     }> |- _ => tt H
  end.

Ltac inv_noref  := _noref inv.
Ltac invc_noref := _noref invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma noref_init_term : forall m t1 t2 ad t,
  no_ref m t1 ->
  t1 --[e_init ad t]--> t2 ->
  no_ref m t.
Proof.
  intros. ind_tstep; invc_noref; eauto.
Qed.

Lemma noref_write_term : forall m t1 t2 ad t,
  no_ref m t1 ->
  t1 --[e_write ad t]--> t2 ->
  no_ref m t.
Proof.
  intros. ind_tstep; invc_noref; eauto.
Qed.

Lemma noref_write_contradiction : forall t1 t2 ad t,
  no_ref ad t1 ->
  t1 --[e_write ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; repeat invc_noref; eauto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma noref_subst : forall ad x tx t,
  no_ref ad t ->
  no_ref ad tx ->
  no_ref ad <{[x := tx] t}>.
Proof. 
  intros. induction t; invc_noref;
  simpl in *; try destruct str_eq_dec; eauto using no_ref.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_noref_preservation :=
  intros; ind_tstep; repeat invc_noref; eauto using noref_subst, no_ref.

Lemma noref_preservation_none : forall ad t1 t2,
  no_ref ad t1 ->
  t1 --[e_none]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_alloc : forall ad t1 t2 ad' T,
  no_ref ad t1 ->
  t1 --[e_alloc ad' T]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_init : forall ad t1 t2 ad' t,
  ad <> ad' ->
  no_ref ad t1 ->
  t1 --[e_init ad' t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_read : forall ad t1 t2 ad' t,
  no_ref ad t ->
  (* --- *)
  no_ref ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_write : forall ad t1 t2 ad' t,
  no_ref ad t1 ->
  t1 --[e_write ad' t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_acq : forall ad t1 t2 ad' t,
  no_ref ad t ->
  (* --- *)
  no_ref ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_rel : forall ad t1 t2 ad',
  no_ref ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_spawn : forall ad t1 t2 tid t,
  no_ref ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_ref ad t2.
Proof. solve_noref_preservation. Qed.

Lemma noref_preservation_spawned : forall ad t1 t2 tid t,
  no_ref ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_ref ad t.
Proof. solve_noref_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* no-wrefs                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive no_wrefs : tm -> Prop :=
  | nowrefs_unit  :                no_wrefs <{unit         }>
  | nowrefs_nat   : forall n,      no_wrefs <{nat n        }>
  | nowrefs_var   : forall x,      no_wrefs <{var x        }>
  | nowrefs_fun   : forall x Tx t, no_wrefs t  ->
                                   no_wrefs <{fn x Tx t    }>
  | nowrefs_call  : forall t1 t2,  no_wrefs t1 ->
                                   no_wrefs t2 ->
                                   no_wrefs <{call t1 t2   }>
  | nowrefs_refR  : forall ad T,   no_wrefs <{&ad : r&T    }>
  | nowrefs_refX  : forall ad T,   no_wrefs <{&ad : x&T    }>
  | nowrefs_new   : forall t T,    no_wrefs t  ->
                                   no_wrefs <{new t : T    }>
  | nowrefs_init  : forall ad t T, no_wrefs t  ->
                                   no_wrefs <{init ad t : T}>
  | nowrefs_load  : forall t,      no_wrefs t  ->
                                   no_wrefs <{*t           }>
  | nowrefs_asg   : forall t1 t2,  no_wrefs t1 ->
                                   no_wrefs t2 ->
                                   no_wrefs <{t1 := t2     }>
  | nowrefs_acq   : forall t1 t2,  no_wrefs t1 ->
                                   no_wrefs t2 ->
                                   no_wrefs <{acq t1 t2    }>
  | nowrefs_cr    : forall ad' t,  no_wrefs t  ->
                                   no_wrefs <{cr ad' t     }>
  | nowrefs_spawn : forall t,      no_wrefs t ->
                                   no_wrefs <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _nowrefs tt :=
  match goal with
  | H : no_wrefs <{unit        }> |- _ => clear H
  | H : no_wrefs <{nat _       }> |- _ => clear H
  | H : no_wrefs <{var _       }> |- _ => clear H
  | H : no_wrefs <{fn _ _ _    }> |- _ => tt H
  | H : no_wrefs <{call _ _    }> |- _ => tt H
  | H : no_wrefs <{&_ : r&_    }> |- _ => clear H
  | H : no_wrefs <{&_ : x&_    }> |- _ => clear H
  | H : no_wrefs <{&_ : w&_    }> |- _ => inv H
  | H : no_wrefs <{new _ : _   }> |- _ => tt H
  | H : no_wrefs <{init _ _ : _}> |- _ => tt H
  | H : no_wrefs <{* _         }> |- _ => tt H
  | H : no_wrefs <{_ := _      }> |- _ => tt H
  | H : no_wrefs <{acq _ _     }> |- _ => tt H
  | H : no_wrefs <{cr _ _      }> |- _ => tt H
  | H : no_wrefs <{spawn _     }> |- _ => tt H
  end.

Ltac inv_nowrefs  := _nowrefs inv.
Ltac invc_nowrefs := _nowrefs invc.

