From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-init                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive no_init (ad : addr) : tm -> Prop :=
  | noinit_unit  :                 no_init ad <{unit          }>
  | noinit_nat   : forall n,       no_init ad <{nat n         }>
  | noinit_var   : forall x,       no_init ad <{var x         }>
  | noinit_fun   : forall x Tx t,  no_init ad t  ->
                                   no_init ad <{fn x Tx t     }>
  | noinit_call  : forall t1 t2,   no_init ad t1 ->
                                   no_init ad t2 ->
                                   no_init ad <{call t1 t2    }>
  | noinit_ref   : forall ad' T,   no_init ad <{&ad' : T      }>
  | noinit_new   : forall T t,     no_init ad t  ->
                                   no_init ad <{new t : T     }>
  | noinit_init  : forall ad' T t, ad <> ad'     ->
                                   no_init ad t  ->
                                   no_init ad <{init ad' t : T}>
  | noinit_load  : forall t,       no_init ad t  ->
                                   no_init ad <{*t            }>
  | noinit_asg   : forall t1 t2,   no_init ad t1 ->
                                   no_init ad t2 ->
                                   no_init ad <{t1 := t2      }>
  | noinit_acq   : forall t1 t2,   no_init ad t1 ->
                                   no_init ad t2 ->
                                   no_init ad <{acq t1 t2     }>
  | noinit_cr    : forall ad' t,   no_init ad t  ->
                                   no_init ad <{cr ad' t      }>
  | noinit_spawn : forall t,       no_init ad t  ->
                                   no_init ad <{spawn t       }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _noinit tt :=
  match goal with
  | H : no_init _   <{unit          }> |- _ => clear H
  | H : no_init _   <{nat _         }> |- _ => clear H
  | H : no_init _   <{var _         }> |- _ => clear H
  | H : no_init _   <{fn _ _ _      }> |- _ => tt H
  | H : no_init _   <{call _ _      }> |- _ => tt H
  | H : no_init _   <{&_ : _        }> |- _ => clear H
  | H : no_init _   <{new _ : _     }> |- _ => tt H
  | H : no_init ?ad <{init ?ad _ : _}> |- _ => invc H; eauto
  | H : no_init _   <{init _ _ : _  }> |- _ => tt H
  | H : no_init _   <{* _           }> |- _ => tt H
  | H : no_init _   <{_ := _        }> |- _ => tt H
  | H : no_init _   <{acq _ _       }> |- _ => tt H
  | H : no_init _   <{cr _ _        }> |- _ => tt H
  | H : no_init _   <{spawn _       }> |- _ => tt H
  end.

Ltac inv_noinit  := _noinit inv.
Ltac invc_noinit := _noinit invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma noinit_init_term : forall t1 t2 ad ad' t,
  no_init ad' t1 ->
  t1 --[e_init ad t]--> t2 ->
  no_init ad' t.
Proof.
  intros. ind_tstep; invc_noinit; eauto using no_init.
Qed.

Lemma noinit_write_term : forall t1 t2 ad ad' t,
  no_init ad' t1 ->
  t1 --[e_write ad t]--> t2 ->
  no_init ad' t.
Proof.
  intros. ind_tstep; invc_noinit; eauto using no_init.
Qed.

Lemma noinit_init_contradiction : forall t1 t2 ad t,
  no_init ad t1 ->
  t1 --[e_init ad t]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_noinit; eauto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma noinit_subst : forall ad x tx t,
  no_init ad t ->
  no_init ad tx ->
  no_init ad <{[x := tx] t}>.
Proof.
  intros. induction t; invc_noinit;
  simpl in *; try destruct str_eq_dec; eauto using no_init.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_noinit_preservation :=
  intros; ind_tstep; repeat invc_noinit; eauto using noinit_subst, no_init.

Lemma noinit_preservation_none : forall ad t1 t2,
  no_init ad t1 ->
  t1 --[e_none]--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_alloc : forall ad t1 t2 ad' T,
  ad <> ad' ->
  no_init ad t1 ->
  t1 --[e_alloc ad' T]--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_init : forall ad t1 t2 ad' t,
  ad <> ad' ->
  no_init ad t1 ->
  t1 --[e_init ad' t]--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_read : forall ad t1 t2 ad' t,
  no_init ad t ->
  (* --- *)
  no_init ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_write : forall ad t1 t2 ad' t,
  no_init ad t1 ->
  t1 --[e_write ad' t]--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_acq : forall ad t1 t2 ad' t,
  no_init ad t ->
  (* --- *)
  no_init ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_rel : forall ad t1 t2 ad',
  no_init ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_spawn : forall ad t1 t2 tid t,
  no_init ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_init ad t2.
Proof. solve_noinit_preservation. Qed.

Lemma noinit_preservation_spawned : forall ad t1 t2 tid t,
  no_init ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_init ad t.
Proof. solve_noinit_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* no-inits                                                                  *)
(* ------------------------------------------------------------------------- *)

Definition no_inits (t : tm) := forall ad, no_init ad t.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_noinits :=
  unfold no_inits; intros; try split; intros; aspecialize; invc_noinit; eauto.

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

Local Lemma inv_noinits_acq : forall t1 t2,
  no_inits <{acq t1 t2}> -> no_inits t1 /\ no_inits t2.
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
  | H : no_inits <{var _       }> |- _ => clear H
  | H : no_inits <{fn _ _ _    }> |- _ => eapply inv_noinits_fun   in H
  | H : no_inits <{call _ _    }> |- _ => eapply inv_noinits_call  in H as [? ?]
  | H : no_inits <{& _ : _     }> |- _ => clear H
  | H : no_inits <{new _ : _   }> |- _ => eapply inv_noinits_new   in H
  | H : no_inits <{init _ _ : _}> |- _ => eapply inv_noinits_init  in H; eauto
  | H : no_inits <{* _         }> |- _ => eapply inv_noinits_load  in H
  | H : no_inits <{_ := _      }> |- _ => eapply inv_noinits_asg   in H as [? ?]
  | H : no_inits <{acq _ _     }> |- _ => eapply inv_noinits_acq   in H as [? ?]
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

Corollary noinits_write_term : forall t1 t2 ad t,
  no_inits t1 ->
  t1 --[e_write ad t]--> t2 ->
  no_inits t.
Proof.
  unfold no_inits. eauto using noinit_write_term.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Corollary noinits_subst : forall x tx t,
  no_inits t ->
  no_inits tx ->
  no_inits <{[x := tx] t}>.
Proof.
  intros ** ?. eauto using noinit_subst.
Qed.

(* ------------------------------------------------------------------------- *)
(* no-cr                                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive no_cr (ad : addr) : tm -> Prop :=
  | nocr_unit  :                 no_cr ad <{unit          }>
  | nocr_nat   : forall n,       no_cr ad <{nat n         }>
  | nocr_var   : forall x,       no_cr ad <{var x         }>
  | nocr_fun   : forall x Tx t,  no_cr ad t  ->
                                 no_cr ad <{fn x Tx t     }>
  | nocr_call  : forall t1 t2,   no_cr ad t1 ->
                                 no_cr ad t2 ->
                                 no_cr ad <{call t1 t2    }>
  | nocr_ref   : forall ad' T,   no_cr ad <{&ad' : T      }>
  | nocr_new   : forall t T,     no_cr ad t  ->
                                 no_cr ad <{new t : T     }>
  | nocr_init  : forall ad' t T, no_cr ad t  ->
                                 no_cr ad <{init ad' t : T}>
  | nocr_load  : forall t,       no_cr ad t  ->
                                 no_cr ad <{*t            }>
  | nocr_asg   : forall t1 t2,   no_cr ad t1 ->
                                 no_cr ad t2 ->
                                 no_cr ad <{t1 := t2      }>
  | nocr_acq   : forall t1 t2,   no_cr ad t1 ->
                                 no_cr ad t2 ->
                                 no_cr ad <{acq t1 t2     }>
  | nocr_cr    : forall ad' t,   ad <> ad'   ->
                                 no_cr ad t  ->
                                 no_cr ad <{cr ad' t      }>
  | nocr_spawn : forall t,       no_cr ad t  ->
                                 no_cr ad <{spawn t       }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _nocr tt :=
  match goal with
  | H : no_cr _   <{unit        }> |- _ => clear H
  | H : no_cr _   <{nat _       }> |- _ => clear H
  | H : no_cr _   <{var _       }> |- _ => clear H
  | H : no_cr _   <{fn _ _ _    }> |- _ => tt H
  | H : no_cr _   <{call _ _    }> |- _ => tt H
  | H : no_cr _   <{&_ : _      }> |- _ => clear H
  | H : no_cr _   <{new _ : _   }> |- _ => tt H
  | H : no_cr _   <{init _ _ : _}> |- _ => tt H
  | H : no_cr _   <{* _         }> |- _ => tt H
  | H : no_cr _   <{_ := _      }> |- _ => tt H
  | H : no_cr _   <{acq _ _     }> |- _ => tt H
  | H : no_cr ?ad <{cr ?ad _    }> |- _ => invc H; eauto
  | H : no_cr _   <{cr _ _      }> |- _ => tt H
  | H : no_cr _   <{spawn _     }> |- _ => tt H
  end.

Ltac inv_nocr  := _nocr inv.
Ltac invc_nocr := _nocr invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma nocr_rel_contradiction : forall t1 t2 ad,
  no_cr ad t1 ->
  t1 --[e_rel ad]--> t2 ->
  False.
Proof.
  intros. ind_tstep; invc_nocr; auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma nocr_subst : forall ad x tx t,
  no_cr ad t ->
  no_cr ad tx ->
  no_cr ad <{[x := tx] t}>.
Proof.
  intros. induction t; simpl in *; trivial;
  try (destruct str_eq_dec; subst); trivial;
  invc_nocr; eauto using no_cr.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_nocr_preservation :=
  intros; ind_tstep; repeat invc_nocr; eauto using nocr_subst, no_cr.

Lemma nocr_preservation_none : forall t1 t2 ad,
  no_cr ad t1 ->
  t1 --[e_none]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_alloc : forall t1 t2 ad ad' T,
  no_cr ad t1 ->
  t1 --[e_alloc ad' T]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_init : forall t1 t2 ad ad' t,
  no_cr ad t1 ->
  t1 --[e_init ad' t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_read : forall t1 t2 ad ad' t,
  no_cr ad t ->
  (* --- *)
  no_cr ad t1 ->
  t1 --[e_read ad' t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_write : forall t1 t2 ad ad' t,
  no_cr ad t1 ->
  t1 --[e_write ad' t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_acq : forall t1 t2 ad ad' t,
  no_cr ad t ->
  (* --- *)
  ad <> ad' ->
  no_cr ad t1 ->
  t1 --[e_acq ad' t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_rel : forall t1 t2 ad ad',
  ad <> ad' ->
  no_cr ad' t1 ->
  t1 --[e_rel ad]--> t2 ->
  no_cr ad' t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_spawn : forall t1 t2 ad tid t,
  no_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_cr ad t2.
Proof. solve_nocr_preservation. Qed.

Lemma nocr_preservation_spawned : forall t1 t2 ad tid t,
  no_cr ad t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_cr ad t.
Proof. solve_nocr_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* no-crs                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition no_crs (t : tm) := forall ad, no_cr ad t.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_nocrs :=
  unfold no_crs; intros * H; try split;
  intros **; auto_specialize; invc_nocr; eauto.

Local Lemma inv_nocrs_fun : forall x Tx t,
  no_crs <{fn x Tx t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_call : forall t1 t2,
  no_crs <{call t1 t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_new : forall t T,
  no_crs <{new t : T}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_init : forall ad t T,
  no_crs <{init ad t : T}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_load : forall t,
  no_crs <{*t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_asg : forall t1 t2,
  no_crs <{t1 := t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_acq : forall t1 t2,
  no_crs <{acq t1 t2}> -> no_crs t1 /\ no_crs t2.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_cr : forall ad t,
  no_crs <{cr ad t}> -> False.
Proof. solve_inv_nocrs. Qed.

Local Lemma inv_nocrs_spawn : forall t,
  no_crs <{spawn t}> -> no_crs t.
Proof. solve_inv_nocrs. Qed.

Ltac invc_nocrs :=
  match goal with
  | H : no_crs <{unit        }> |- _ => clear H
  | H : no_crs <{nat _       }> |- _ => clear H
  | H : no_crs <{var _       }> |- _ => clear H
  | H : no_crs <{fn _ _ _    }> |- _ => eapply inv_nocrs_fun    in H
  | H : no_crs <{call _ _    }> |- _ => eapply inv_nocrs_call   in H as [? ?]
  | H : no_crs <{& _ : _     }> |- _ => clear H
  | H : no_crs <{new _ : _   }> |- _ => eapply inv_nocrs_new    in H
  | H : no_crs <{init _ _ : _}> |- _ => eapply inv_nocrs_init   in H
  | H : no_crs <{* _         }> |- _ => eapply inv_nocrs_load   in H
  | H : no_crs <{_ := _      }> |- _ => eapply inv_nocrs_asg    in H as [? ?]
  | H : no_crs <{acq _ _     }> |- _ => eapply inv_nocrs_acq    in H as [? ?]
  | H : no_crs <{cr _ _      }> |- _ => eapply inv_nocrs_cr     in H; eauto
  | H : no_crs <{spawn _     }> |- _ => eapply inv_nocrs_spawn  in H
  end.

(* lemmas ------------------------------------------------------------------ *)

Corollary nocr_from_nocrs : forall ad t,
  no_crs t ->
  no_cr ad t.
Proof.
  unfold no_crs. auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Corollary nocrs_subst : forall x tx t,
  no_crs t ->
  no_crs tx ->
  no_crs <{[x := tx] t}>.
Proof.
  intros ** ?. eauto using nocr_subst.
Qed.

(* ------------------------------------------------------------------------- *)
(* valid-blocks                                                              *)
(* ------------------------------------------------------------------------- *)

Inductive valid_blocks : tm -> Prop :=
  | vb_unit  :                valid_blocks <{unit      }>
  | vb_nat   : forall n,      valid_blocks <{nat n     }>
  | vb_var   : forall x,      valid_blocks <{var x     }>
  | vb_fun   : forall x Tx t, no_inits t      ->
                              no_crs   t      ->
                              valid_blocks <{fn x Tx t }>
  | vb_call  : forall t1 t2,  valid_blocks t1 ->
                              valid_blocks t2 ->
                              valid_blocks <{call t1 t2}>
  | vb_ref   : forall ad T,   valid_blocks <{&ad : T   }>
  | vb_new   : forall T t,    valid_blocks t  ->
                              valid_blocks <{new t : T }>
  | vb_init  : forall ad T t, valid_blocks t  ->
                              valid_blocks <{init ad t : T }>
  | vb_load  : forall t,      valid_blocks t  ->
                              valid_blocks <{*t        }>
  | vb_asg   : forall t1 t2,  valid_blocks t1 ->
                              valid_blocks t2 ->
                              valid_blocks <{t1 := t2  }>
  | vb_acq   : forall t1 t2,  valid_blocks t1 ->
                              valid_blocks t2 ->
                              valid_blocks <{acq t1 t2 }>
  | vb_cr    : forall ad t,   valid_blocks t  ->
                              valid_blocks <{cr ad t   }>
  | vb_spawn : forall t,      no_inits t      ->
                              no_crs   t      ->
                              valid_blocks <{spawn t   }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vb tt :=
  match goal with
  | H : valid_blocks <{unit          }> |- _ => clear H
  | H : valid_blocks <{nat _         }> |- _ => clear H
  | H : valid_blocks <{var _         }> |- _ => clear H
  | H : valid_blocks <{fn _ _ _      }> |- _ => tt H
  | H : valid_blocks <{call _ _      }> |- _ => tt H
  | H : valid_blocks <{&_ : _        }> |- _ => clear H
  | H : valid_blocks <{new _ : _     }> |- _ => tt H
  | H : valid_blocks <{init _ _ : _  }> |- _ => tt H
  | H : valid_blocks <{* _           }> |- _ => tt H
  | H : valid_blocks <{_ := _        }> |- _ => tt H
  | H : valid_blocks <{acq _ _       }> |- _ => tt H
  | H : valid_blocks <{cr _ _        }> |- _ => tt H
  | H : valid_blocks <{spawn _       }> |- _ => tt H
  end.

Ltac inv_vb  := _vb inv.
Ltac invc_vb := _vb invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vb_init_term : forall t1 t2 ad t,
  valid_blocks t1 ->
  t1 --[e_init ad t]--> t2 ->
  valid_blocks t.
Proof.
  intros. ind_tstep; invc_vb; eauto using valid_blocks.
Qed.

Lemma vb_write_term : forall t1 t2 ad t,
  valid_blocks t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_blocks t.
Proof.
  intros. ind_tstep; invc_vb; eauto using valid_blocks.
Qed.

Lemma noinit_spawn_term : forall m t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_init m t.
Proof.
  intros. ind_tstep; invc_vb; auto.
Qed.

Lemma nocrs_spawn_term : forall t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  no_crs t.
Proof.
  intros. ind_tstep; invc_vb; auto.
Qed.

Lemma noinit_from_value : forall ad t,
  valid_blocks t ->
  (* --- *)
  value t ->
  no_init ad t.
Proof.
  intros * ? Hval. invc Hval; invc_vb; eauto using no_init.
Qed.

Lemma nocr_from_value : forall ad t,
  valid_blocks t ->
  (* --- *)
  value t ->
  no_cr ad t.
Proof.
  intros * ? Hval. invc Hval; invc_vb; eauto using no_cr.
Qed.

Corollary noinits_from_value : forall t,
  valid_blocks t ->
  (* --- *)
  value t ->
  no_inits t.
Proof.
  intros ** ?. eauto using noinit_from_value.
Qed.

Corollary nocrs_from_value : forall t,
  valid_blocks t ->
  (* --- *)
  value t ->
  no_crs t.
Proof.
  intros ** ?. eauto using nocr_from_value.
Qed.

Lemma vb_from_noinits_nocrs : forall t,
  no_inits t ->
  no_crs   t ->
  valid_blocks t.
Proof.
  intros. induction t; invc_noinits; invc_nocrs; eauto using valid_blocks.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma vb_subst : forall x tx t,
  no_inits t ->
  no_crs   t ->
  value tx ->
  valid_blocks tx ->
  valid_blocks <{[x := tx] t}>.
Proof.
  intros. induction t; invc_noinits; invc_nocrs;
  simpl; try destruct str_eq_dec; subst; eauto using valid_blocks;
  constructor;
  eauto using noinits_from_value, noinits_subst;
  eauto using nocrs_from_value, nocrs_subst.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_vb_preservation :=
  intros; ind_tstep; repeat invc_vb;
  eauto using vb_from_noinits_nocrs, vb_subst, valid_blocks.

Lemma vb_preservation_none : forall t1 t2,
  valid_blocks t1 ->
  t1 --[e_none]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_alloc : forall t1 t2 ad T,
  valid_blocks t1 ->
  t1 --[e_alloc ad T]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_init : forall t1 t2 ad t,
  valid_blocks t1 ->
  t1 --[e_init ad t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_read : forall t1 t2 ad t,
  valid_blocks t ->
  (* --- *)
  valid_blocks t1 ->
  t1 --[e_read ad t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_write : forall t1 t2 ad t,
  valid_blocks t1 ->
  t1 --[e_write ad t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_acq : forall t1 t2 ad t,
  value t ->
  valid_blocks t ->
  (* --- *)
  valid_blocks t1 ->
  t1 --[e_acq ad t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_rel : forall t1 t2 ad,
  valid_blocks t1 ->
  t1 --[e_rel ad]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_spawn : forall t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_blocks t2.
Proof. solve_vb_preservation. Qed.

Lemma vb_preservation_spawned : forall t1 t2 tid t,
  valid_blocks t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  valid_blocks t.
Proof. solve_vb_preservation. Qed.

Theorem vb_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_memory m1 value ->
  (* --- *)
  forall_program m1 ths1 valid_blocks ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_program m2 ths2 valid_blocks.
Proof.
  intros * ? Hvb ?.
  assert (Hvb' := Hvb). destruct Hvb as [? ?].
  invc_cstep; try invc_mstep; upsilon.
  - eauto using vb_preservation_none.
  - eauto using vb_preservation_alloc.
  - eauto using vb_init_term, vb_preservation_init.
  - eauto using vb_preservation_read.
  - eauto using vb_write_term, vb_preservation_write.
  - eauto using vb_preservation_acq.
  - eauto using vb_preservation_rel.
  - eauto using vb_preservation_spawn, vb_preservation_spawned.
Qed.




(* inheritance ------------------------------------------------------------- *)

Local Lemma noinit_inheritance_subst : forall x Tx t tx ad,
  no_init ad tx ->
  no_init ad <{[x := tx] t}> ->
  no_init ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. repeat constructor; trivial.
  induction t; simpl in *;
  try destruct str_eq_dec; try invc_noinit; eauto using no_init.
Qed.

Lemma noinit_inheritance_none : forall ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_init ad t2 ->
  t1 --[e_none]--> t2 ->
  no_init ad t1.
Proof.
  intros. ind_tstep; repeat invc_vb; try invc_noinit; eauto using no_init.
  eauto using noinit_from_value, noinit_inheritance_subst.
Qed.

Local Lemma nocr_inheritance_subst : forall x Tx t tx ad,
  no_cr ad tx ->
  no_cr ad <{[x := tx] t}> ->
  no_cr ad <{call <{fn x Tx t}> tx}>.
Proof.
  intros. repeat constructor; trivial.
  induction t; simpl in *;
  try destruct str_eq_dec; try invc_nocr; eauto using no_cr.
Qed.

Lemma nocr_inheritance_none : forall ad t1 t2,
  valid_blocks t1 ->
  (* --- *)
  no_cr ad t2 ->
  t1 --[e_none]--> t2 ->
  no_cr ad t1.
Proof.
  intros. ind_tstep; repeat invc_vb; try invc_nocr; eauto using no_cr.
  eauto using nocr_from_value, nocr_inheritance_subst.
Qed.

