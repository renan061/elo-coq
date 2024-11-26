From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-wref                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive no_wref (ad : addr) : tm -> Prop :=
  | nowref_unit  :                 no_wref ad <{unit         }>
  | nowref_nat   : forall n,       no_wref ad <{nat n        }>
  | nowref_var   : forall x,       no_wref ad <{var x        }>
  | nowref_fun   : forall x Tx t,  no_wref ad t  ->
                                   no_wref ad <{fn x Tx t    }>
  | nowref_call  : forall t1 t2,   no_wref ad t1 ->
                                   no_wref ad t2 ->
                                   no_wref ad <{call t1 t2   }>
  | nowref_refR  : forall ad' T,   no_wref ad <{&ad' : r&T    }>
  | nowref_refX  : forall ad' T,   no_wref ad <{&ad' : x&T    }>
  | nowref_refW  : forall ad' T,   ad <> ad'     ->
                                   no_wref ad <{&ad' : r&T    }>
  | nowref_new   : forall t T,     no_wref ad t  ->
                                   no_wref ad <{new t : T    }>
  | nowref_init  : forall ad' t T, no_wref ad t  ->
                                   no_wref ad <{init ad' t : T}>
  | nowref_load  : forall t,       no_wref ad t  ->
                                   no_wref ad <{*t           }>
  | nowref_asg   : forall t1 t2,   no_wref ad t1 ->
                                   no_wref ad t2 ->
                                   no_wref ad <{t1 := t2     }>
  | nowref_acq   : forall t1 t2,   no_wref ad t1 ->
                                   no_wref ad t2 ->
                                   no_wref ad <{acq t1 t2    }>
  | nowref_cr    : forall ad' t,   no_wref ad t  ->
                                   no_wref ad <{cr ad' t     }>
  | nowref_spawn : forall t,       no_wref ad t  ->
                                   no_wref ad <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _nowref tt :=
  match goal with
  | H : no_wref _ <{unit        }> |- _ => clear H
  | H : no_wref _ <{nat _       }> |- _ => clear H
  | H : no_wref _ <{var _       }> |- _ => clear H
  | H : no_wref _ <{fn _ _ _    }> |- _ => tt H
  | H : no_wref _ <{call _ _    }> |- _ => tt H
  | H : no_wref _ <{&_ : r&_    }> |- _ => clear H
  | H : no_wref _ <{&_ : x&_    }> |- _ => clear H
  | H : no_wref _ <{&_ : w&_    }> |- _ => tt H
  | H : no_wref _ <{new _ : _   }> |- _ => tt H
  | H : no_wref _ <{init _ _ : _}> |- _ => tt H
  | H : no_wref _ <{* _         }> |- _ => tt H
  | H : no_wref _ <{_ := _      }> |- _ => tt H
  | H : no_wref _ <{acq _ _     }> |- _ => tt H
  | H : no_wref _ <{cr _ _      }> |- _ => tt H
  | H : no_wref _ <{spawn _     }> |- _ => tt H
  end.

Ltac inv_nowref  := _nowref inv.
Ltac invc_nowref := _nowref invc.

(* ------------------------------------------------------------------------- *)
(* no-wrefs                                                                  *)
(* ------------------------------------------------------------------------- *)

Definition no_wrefs (t : tm) := forall ad, no_wref ad t.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_nowrefs :=
  unfold no_wrefs; intros; try split; intros; aspecialize; invc_nowref; eauto.

Local Lemma inv_nowrefs_fun : forall x Tx t,
  no_wrefs <{fn x Tx t}> -> no_wrefs t.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_call : forall t1 t2,
  no_wrefs <{call t1 t2}> -> no_wrefs t1 /\ no_wrefs t2.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_refW : forall ad T,
  no_wrefs <{&ad : w&T}> -> False.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_new : forall t T,
  no_wrefs <{new t : T}> -> no_wrefs t.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_init : forall ad t T,
  no_wrefs <{init ad t : T}> -> no_wrefs t.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_load : forall t,
  no_wrefs <{*t}> -> no_wrefs t.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_asg : forall t1 t2,
  no_wrefs <{t1 := t2}> -> no_wrefs t1 /\ no_wrefs t2.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_acq : forall t1 t2,
  no_wrefs <{acq t1 t2}> -> no_wrefs t1 /\ no_wrefs t2.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_cr : forall ad t,
  no_wrefs <{cr ad t}> -> no_wrefs t.
Proof. solve_inv_nowrefs. Qed.

Local Lemma inv_nowrefs_spawn : forall t,
  no_wrefs <{spawn t}> -> no_wrefs t.
Proof. solve_inv_nowrefs. Qed.

Ltac invc_nowrefs :=
  match goal with
  | H : no_wrefs <{unit        }> |- _ => clear H
  | H : no_wrefs <{nat _       }> |- _ => clear H
  | H : no_wrefs <{var _       }> |- _ => clear H
  | H : no_wrefs <{fn _ _ _    }> |- _ => eapply inv_nowrefs_fun   in H
  | H : no_wrefs <{call _ _    }> |- _ => eapply inv_nowrefs_call  in H as [? ?]
  | H : no_wrefs <{& _ : w&_   }> |- _ => eapply inv_nowrefs_refW  in H; eauto
  | H : no_wrefs <{& _ : _     }> |- _ => clear H
  | H : no_wrefs <{new _ : _   }> |- _ => eapply inv_nowrefs_new   in H
  | H : no_wrefs <{init _ _ : _}> |- _ => eapply inv_nowrefs_init  in H
  | H : no_wrefs <{* _         }> |- _ => eapply inv_nowrefs_load  in H
  | H : no_wrefs <{_ := _      }> |- _ => eapply inv_nowrefs_asg   in H as [? ?]
  | H : no_wrefs <{acq _ _     }> |- _ => eapply inv_nowrefs_acq   in H as [? ?]
  | H : no_wrefs <{cr _ _      }> |- _ => eapply inv_nowrefs_cr    in H
  | H : no_wrefs <{spawn _     }> |- _ => eapply inv_nowrefs_spawn in H
  end.

