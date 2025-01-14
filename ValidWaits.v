From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-waits                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive no_waits : tm -> Prop :=
  | nowaits_unit   :                  no_waits <{unit                     }>
  | nowaits_nat    : forall n,        no_waits <{nat n                    }>
  | nowaits_plus   : forall t1 t2,    no_waits t1 ->
                                      no_waits t2 ->
                                      no_waits <{t1 + t2                  }>
  | nowaits_monus  : forall t1 t2,    no_waits t1 ->
                                      no_waits t2 ->
                                      no_waits <{t1 - t2                  }>
  | nowaits_seq    : forall t1 t2,    no_waits t1 ->
                                      no_waits t2 ->
                                      no_waits <{t1; t2                   }>
  | nowaits_if     : forall t1 t2 t3, no_waits t1 ->
                                      no_waits t2 ->
                                      no_waits t3 ->
                                      no_waits <{if t1 then t2 else t3 end}>
  | nowaits_while  : forall t1 t2,    no_waits t1 ->
                                      no_waits t2 ->
                                      no_waits <{while t1 do t2 end}>
  | nowaits_var    : forall x,        no_waits <{var x                    }>
  | nowaits_fun    : forall x Tx t,   no_waits t           ->
                                      no_waits <{fn x Tx t                }>
  | nowaits_call   : forall t1 t2,    no_waits t1 ->
                                      no_waits t2 ->
                                      no_waits <{call t1 t2               }>
  | nowaits_ref    : forall ad T,     no_waits <{&ad : T                  }>
  | nowaits_new    : forall t T,      no_waits t  ->
                                      no_waits <{new t : T                }>
  | nowaits_init   : forall ad t T,   no_waits t  ->
                                      no_waits <{init ad t : T            }>
  | nowaits_load   : forall t,        no_waits t  ->
                                      no_waits <{*t                       }>
  | nowaits_asg    : forall t1 t2,    no_waits t1 ->
                                      no_waits t2 ->
                                      no_waits <{t1 := t2                 }>
  | nowaits_acq    : forall t1 x t2,  no_waits t1 ->
                                      no_waits t2 ->
                                      no_waits <{acq t1 x t2              }>
  | nowaits_cr     : forall ad t,     no_waits  t ->
                                      no_waits <{cr ad t                  }>
  | nowaits_reacq  : forall ad,       no_waits <{reacq ad                 }>
  | nowaits_spawn  : forall t,        no_waits t  ->
                                      no_waits <{spawn t                  }>
  .

Local Ltac _nowaits tt :=
  match goal with
  | H : no_waits <{unit                  }> |- _ => clear H
  | H : no_waits <{nat _                 }> |- _ => clear H
  | H : no_waits <{_ + _                 }> |- _ => tt H
  | H : no_waits <{_ - _                 }> |- _ => tt H
  | H : no_waits <{_; _                  }> |- _ => tt H
  | H : no_waits <{if _ then _ else _ end}> |- _ => tt H
  | H : no_waits <{while _ do _ end      }> |- _ => tt H
  | H : no_waits <{var _                 }> |- _ => tt H
  | H : no_waits <{fn _ _ _              }> |- _ => tt H
  | H : no_waits <{call _ _              }> |- _ => tt H
  | H : no_waits <{&_ : _                }> |- _ => clear H
  | H : no_waits <{new _ : _             }> |- _ => tt H
  | H : no_waits <{init _ _ : _          }> |- _ => tt H
  | H : no_waits <{* _                   }> |- _ => tt H
  | H : no_waits <{_ := _                }> |- _ => tt H
  | H : no_waits <{acq _ _ _             }> |- _ => tt H
  | H : no_waits <{cr _ _                }> |- _ => tt H
  | H : no_waits <{wait _                }> |- _ => invc H
  | H : no_waits <{reacq _               }> |- _ => clear H
  | H : no_waits <{spawn _               }> |- _ => tt H
  end.

Ltac inv_nowaits  := _nowaits inv.
Ltac invc_nowaits := _nowaits invc.

(* preservation lemmas ----------------------------------------------------- *)

Lemma nowaits_subst : forall t tx x,
  no_waits t  ->
  no_waits tx ->
  no_waits <{[x := tx] t}>.
Proof.
  intros. induction t; invc_nowaits; simpl; try destruct _str_eq_dec;
  auto using no_waits.
Qed.

(* ------------------------------------------------------------------------- *)
(* matching-waits                                                            *)
(* ------------------------------------------------------------------------- *)

Inductive matching_waits (ad : addr) : tm -> Prop :=
  | mwaits_unit   :                  matching_waits ad <{unit              }>
  | mwaits_nat    : forall n,        matching_waits ad <{nat n             }>
  | mwaits_plus   : forall t1 t2,    matching_waits ad t1 ->
                                     matching_waits ad t2 ->
                                     matching_waits ad <{t1 + t2           }>
  | mwaits_monus  : forall t1 t2,    matching_waits ad t1 ->
                                     matching_waits ad t2 ->
                                     matching_waits ad <{t1 - t2           }>
  | mwaits_seq    : forall t1 t2,    matching_waits ad t1 ->
                                     matching_waits ad t2 ->
                                     matching_waits ad <{t1; t2            }>
  | mwaits_if     : forall t1 t2 t3, matching_waits ad t1 ->
                                     matching_waits ad t2 ->
                                     matching_waits ad t3 ->
                                     matching_waits ad (tm_if t1 t2 t3)
  | mwaits_while  : forall t1 t2,    matching_waits ad t1 ->
                                     matching_waits ad t2 ->
                                     matching_waits ad <{while t1 do t2 end}>
  | mwaits_var    : forall x,        matching_waits ad <{var x             }>
  | mwaits_fun    : forall x Tx t,   no_waits t           ->
                                     matching_waits ad <{fn x Tx t         }>
  | mwaits_call   : forall t1 t2,    matching_waits ad t1 ->
                                     matching_waits ad t2 ->
                                     matching_waits ad <{call t1 t2        }>
  | mwaits_ref    : forall ad' T,    matching_waits ad <{&ad' : T          }>
  | mwaits_new    : forall t T,      matching_waits ad t  ->
                                     matching_waits ad <{new t : T         }>
  | mwaits_init   : forall ad' t T,  matching_waits ad t  ->
                                     matching_waits ad <{init ad' t : T    }>
  | mwaits_load   : forall t,        matching_waits ad t  ->
                                     matching_waits ad <{*t                }>
  | mwaits_asg    : forall t1 t2,    matching_waits ad t1 ->
                                     matching_waits ad t2 ->
                                     matching_waits ad <{t1 := t2          }>
  | mwaits_acq    : forall t1 x t2,  matching_waits ad t1 ->
                                     matching_waits ad <{acq t1 x t2       }>
  | mwaits_cr     : forall ad' t,    matching_waits ad' t ->
                                     matching_waits ad <{cr ad' t          }>
  | mwaits_wait   :                  matching_waits ad <{wait ad           }>
  | mwaits_reacq  : forall ad',      matching_waits ad <{reacq ad'         }>
  | mwaits_spawn  : forall t,        matching_waits ad t  ->
                                     matching_waits ad <{spawn t           }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _mwaits tt :=
  match goal with
  | H : matching_waits _ <{unit                  }> |- _ => clear H
  | H : matching_waits _ <{nat _                 }> |- _ => clear H
  | H : matching_waits _ <{_ + _                 }> |- _ => tt H
  | H : matching_waits _ <{_ - _                 }> |- _ => tt H
  | H : matching_waits _ <{_; _                  }> |- _ => tt H
  | H : matching_waits _ <{if _ then _ else _ end}> |- _ => tt H
  | H : matching_waits _ <{while _ do _ end      }> |- _ => tt H
  | H : matching_waits _ <{var _                 }> |- _ => tt H
  | H : matching_waits _ <{fn _ _ _              }> |- _ => tt H
  | H : matching_waits _ <{call _ _              }> |- _ => tt H
  | H : matching_waits _ <{&_ : _                }> |- _ => clear H
  | H : matching_waits _ <{new _ : _             }> |- _ => tt H
  | H : matching_waits _ <{init _ _ : _          }> |- _ => tt H
  | H : matching_waits _ <{* _                   }> |- _ => tt H
  | H : matching_waits _ <{_ := _                }> |- _ => tt H
  | H : matching_waits _ <{acq _ _ _             }> |- _ => tt H
  | H : matching_waits _ <{cr _ _                }> |- _ => tt H
  | H : matching_waits _ <{wait _                }> |- _ => tt H
  | H : matching_waits _ <{reacq _               }> |- _ => clear H
  | H : matching_waits _ <{spawn _               }> |- _ => tt H
  end.

Ltac inv_mwaits  := _mwaits inv.
Ltac invc_mwaits := _mwaits invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma mwaits_from_nowaits : forall ad t,
  no_waits t ->
  matching_waits ad t.
Proof.
  intros. gendep ad.
  induction t; intros; invc_nowaits; auto using matching_waits.
Qed.

Lemma nowaits_from_value1 : forall ad t,
  matching_waits ad t ->
  (* --- *)
  value t ->
  no_waits t.
Proof.
  intros * ? Hval. invc Hval; auto using no_waits.
  invc_mwaits. auto using no_waits.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma mwaits_subst : forall ad t tx x,
  value tx ->
  (* --- *)
  no_waits t ->
  matching_waits ad tx ->
  matching_waits ad <{[x := tx] t}>.
Proof.
  intros. eauto using mwaits_from_nowaits, nowaits_from_value1, nowaits_subst. 
Qed.

Lemma mwaits_fw : forall ad t,
  matching_waits ad (fw ad t).
Proof.
  intros. gendep ad. induction t; intros; simpl; auto using matching_waits.
  - constructor. admit.
  - repeat spec. constructor. admit.
Abort.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_mwaits_preservation :=
  intros ad **; gendep ad;
  ind_tstep; intros; repeat invc_mwaits; repeat constructor;
  auto using mwaits_from_nowaits, mwaits_subst.

Lemma mwaits_preservation_none : forall ad t1 t2,
  matching_waits ad t1 ->
  t1 --[e_none]--> t2 ->
  matching_waits ad t2.
Proof. solve_mwaits_preservation. Qed.

Lemma mwaits_preservation_alloc : forall ad t1 t2 ad' T',
  matching_waits ad t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  matching_waits ad t2.
Proof. solve_mwaits_preservation. Qed.

Lemma mwaits_preservation_init : forall ad t1 t2 ad' t',
  matching_waits ad t1 ->
  t1 --[e_init ad' t']--> t2 ->
  matching_waits ad t2.
Proof. solve_mwaits_preservation. Qed.

Lemma mwaits_preservation_read : forall ad t1 t2 ad' t',
  no_waits t' ->
  (* --- *)
  matching_waits ad t1 ->
  t1 --[e_read ad' t']--> t2 ->
  matching_waits ad t2.
Proof. solve_mwaits_preservation. Qed.

Lemma mwaits_preservation_write : forall ad t1 t2 ad' t',
  matching_waits ad t1 ->
  t1 --[e_write ad' t']--> t2 ->
  matching_waits ad t2.
Proof. solve_mwaits_preservation. Qed.

Lemma mwaits_preservation_acq : forall ad t1 t2 ad' t' T,
  no_waits t' ->
  empty |-- t1 is T ->
  (* --- *)
  matching_waits ad t1 ->
  t1 --[e_acq ad' t']--> t2 ->
  matching_waits ad t2.
Proof.
  intros ad **. gendep ad. gendep T.
  ind_tstep; intros; invc_typeof; repeat invc_mwaits; repeat constructor;
  eauto using mwaits_from_nowaits, mwaits_subst.
  rewrite <- empty_eq_safe_empty in *.
  invc_typeof.
  assert (~ (exists x' Tx' t', t = <{fn x' Tx' t'}>)). {
    intros [? [? [? ?]]]. subst. invc_typeof.
  }
Qed.

Lemma mwaits_preservation_rel : forall ad t1 t2 ad',
  matching_waits ad t1 ->
  t1 --[e_rel ad']--> t2 ->
  matching_waits ad t2.
Proof. solve_mwaits_preservation. Qed.

(* ------------------------------------------------------------------------- *)
(* valid-waits                                                               *)
(* ------------------------------------------------------------------------- *)

Inductive valid_waits : tm -> Prop :=
  | vwaits_unit   :                  valid_waits <{unit                     }>
  | vwaits_nat    : forall n,        valid_waits <{nat n                    }>
  | vwaits_plus   : forall t1 t2,    valid_waits t1 ->
                                     valid_waits t2 ->
                                     valid_waits <{t1 + t2                  }>
  | vwaits_monus  : forall t1 t2,    valid_waits t1 ->
                                     valid_waits t2 ->
                                     valid_waits <{t1 - t2                  }>
  | vwaits_seq    : forall t1 t2,    valid_waits t1 ->
                                     valid_waits t2 ->
                                     valid_waits <{t1; t2                   }>
  | vwaits_if     : forall t1 t2 t3, valid_waits t1 ->
                                     valid_waits t2 ->
                                     valid_waits t3 ->
                                     valid_waits <{if t1 then t2 else t3 end}>
  | vwaits_while  : forall t1 t2,    valid_waits t1 ->
                                     valid_waits t2 ->
                                     valid_waits <{while t1 do t2 end       }>
  | vwaits_var    : forall x,        valid_waits <{var x                    }>
  | vwaits_fun    : forall x Tx t,   no_waits t     ->
                                     valid_waits <{fn x Tx t                }>
  | vwaits_call   : forall t1 t2,    valid_waits t1 ->
                                     valid_waits t2 ->
                                     valid_waits <{call t1 t2               }>
  | vwaits_ref    : forall ad T,     valid_waits <{&ad : T                  }>
  | vwaits_new    : forall t T,      valid_waits t  ->
                                     valid_waits <{new t : T                }>
  | vwaits_init   : forall ad t T,   valid_waits t  ->
                                     valid_waits <{init ad t : T            }>
  | vwaits_load   : forall t,        valid_waits t  ->
                                     valid_waits <{*t                       }>
  | vwaits_asg    : forall t1 t2,    valid_waits t1 ->
                                     valid_waits t2 ->
                                     valid_waits <{t1 := t2                 }>
  | vwaits_acq    : forall t1 x t2,  valid_waits t1 ->
                                     valid_waits <{acq t1 x t2              }>
  | vwaits_cr     : forall ad t,     matching_waits ad t ->
                                     valid_waits <{cr ad t                  }>
  | vwaits_reacq  : forall ad',      valid_waits <{reacq ad'                }>
  | vwaits_spawn  : forall t,        valid_waits t  ->
                                     valid_waits <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _vwaits tt :=
  match goal with
  | H : valid_waits <{unit                  }> |- _ => clear H
  | H : valid_waits <{nat _                 }> |- _ => clear H
  | H : valid_waits <{_ + _                 }> |- _ => tt H
  | H : valid_waits <{_ - _                 }> |- _ => tt H
  | H : valid_waits <{_; _                  }> |- _ => tt H
  | H : valid_waits <{if _ then _ else _ end}> |- _ => tt H
  | H : valid_waits <{while _ do _ end      }> |- _ => tt H
  | H : valid_waits <{var _                 }> |- _ => tt H
  | H : valid_waits <{fn _ _ _              }> |- _ => tt H
  | H : valid_waits <{call _ _              }> |- _ => tt H
  | H : valid_waits <{&_ : _                }> |- _ => clear H
  | H : valid_waits <{new _ : _             }> |- _ => tt H
  | H : valid_waits <{init _ _ : _          }> |- _ => tt H
  | H : valid_waits <{* _                   }> |- _ => tt H
  | H : valid_waits <{_ := _                }> |- _ => tt H
  | H : valid_waits <{acq _ _ _             }> |- _ => tt H
  | H : valid_waits <{cr _ _                }> |- _ => tt H
  | H : valid_waits <{wait _                }> |- _ => invc H
  | H : valid_waits <{reacq _               }> |- _ => clear H
  | H : valid_waits <{spawn _               }> |- _ => tt H
  end.

Ltac inv_vwaits  := _vwaits inv.
Ltac invc_vwaits := _vwaits invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma vwaits_from_nowaits : forall t,
  no_waits t ->
  valid_waits t.
Proof.
  intros. induction t; invc_nowaits;
  auto using mwaits_from_nowaits, valid_waits.
Qed.

Lemma nowaits_from_value2 : forall t,
  valid_waits t ->
  (* --- *)
  value t ->
  no_waits t.
Proof.
  intros * ? Hval. invc Hval; auto using no_waits.
  invc_vwaits. auto using no_waits.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma vwaits_subst : forall t tx x,
  value tx       ->
  (* --- *)
  no_waits t     ->
  valid_waits tx ->
  valid_waits <{[x := tx] t}>.
Proof.
  eauto using vwaits_from_nowaits, nowaits_from_value2, nowaits_subst.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_vwaits_preservation L :=
  intros; ind_tstep; repeat invc_vwaits; repeat constructor;
  eauto using vwaits_subst, L.

Lemma vwaits_preservation_none : forall t1 t2,
  valid_waits t1 ->
  t1 --[e_none]--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation mwaits_preservation_none. Qed.

Lemma vwaits_preservation_alloc : forall t1 t2 ad' T',
  valid_waits t1 ->
  t1 --[e_alloc ad' T']--> t2 ->
  valid_waits t2.
Proof. solve_vwaits_preservation mwaits_preservation_alloc. Qed.

(* ------------------------------------------------------------------------- *)

Corollary vwaits_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   valid_waits   ->
  forall_threads ths1 valid_waits   ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_threads ths2 valid_waits.
Proof.
  intros. invc_cstep; try invc_mstep; trivial.
  - upsilon. eauto using vtm_preservation_none.
  - upsilon. (* TODO: fix upsilon *)
    intro tid'. sigma. upsilon. omicron.
    + eauto using vtm_preservation_alloc.
    + eauto using vtm_mem_add.
  - upsilon; eauto using vtm_mem_set, vtm_preservation_init.
  - upsilon. eauto using vtm_preservation_read.
  - upsilon; eauto using vtm_mem_set, vtm_preservation_write.
  - upsilon; eauto using vtm_mem_acq, vtm_preservation_acq.
  - upsilon; eauto using vtm_mem_rel, vtm_preservation_rel.
  - upsilon; eauto using vtm_mem_acq, vtm_preservation_wacq.
  - upsilon; eauto using vtm_mem_rel, vtm_preservation_wrel.
  - upsilon; eauto using vtm_preservation_spawn, vtm_preservation_spawned.
Qed.

Theorem vwaits_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_program m1 ths1 valid_waits ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_program m2 ths2 valid_waits.
Proof.
  intros * [? ?] ?. split;
  eauto using vwaits_preservation_memory, vwaits_preservation_threads.
Qed.
