From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* keywords                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
  (!!!) keywords is an initial condition.
  (!!!) keywords is an invariant.
*)
Inductive keywords : tm -> Prop :=
  | kw_unit  :                  keywords <{unit                     }>
  | kw_nat   : forall n,        keywords <{nat n                    }>
  | kw_plus  : forall t1 t2,    keywords t1 ->
                                keywords t2 ->
                                keywords <{t1 + t2                  }>
  | kw_monus : forall t1 t2,    keywords t1 ->
                                keywords t2 ->
                                keywords <{t1 - t2                  }>
  | kw_seq   : forall t1 t2,    keywords t1 ->
                                keywords t2 ->
                                keywords <{t1; t2                   }>
  | kw_if    : forall t1 t2 t3, keywords t1 ->
                                keywords t2 ->
                                keywords t3 ->
                                keywords <{if t1 then t2 else t3 end}>
  | kw_while : forall t1 t2,    keywords t1 ->
                                keywords t2 ->
                                keywords <{while t1 do t2 end       }>
  | kw_var   : forall x,        keywords <{var x                    }>
  | kw_fun   : forall x Tx t,   x <> SELF        ->
                                keywords t  ->
                                keywords <{fn x Tx t                }>
  | kw_call  : forall t1 t2,    keywords t1 ->
                                keywords t2 ->
                                keywords <{call t1 t2               }>
  | kw_ref   : forall ad T,     keywords <{&ad : T                  }>
  | kw_new   : forall t T,      keywords t  ->
                                keywords <{new t : T                }>
  | kw_init  : forall ad t T,   keywords t  ->
                                keywords <{init ad t : T            }>
  | kw_load  : forall t,        keywords t  ->
                                keywords <{*t                       }>
  | kw_asg   : forall t1 t2,    keywords t1 ->
                                keywords t2 ->
                                keywords <{t1 := t2                 }>
  | kw_acq   : forall t1 x t2,  x <> SELF        ->
                                keywords t1 ->
                                keywords t2 ->
                                keywords <{acq t1 x t2              }>
  | kw_cr    : forall ad t,     keywords t  ->
                                keywords <{cr ad t                  }>
  | kw_reacq : forall ad,       keywords <{reacq ad                 }>
  | kw_spawn : forall t,        keywords t ->
                                keywords <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _kw tt :=
  match goal with
  | H : keywords <{unit                  }> |- _ => clear H
  | H : keywords <{nat _                 }> |- _ => clear H
  | H : keywords <{_ + _                 }> |- _ => tt H
  | H : keywords <{_ - _                 }> |- _ => tt H
  | H : keywords <{_; _                  }> |- _ => tt H
  | H : keywords <{if _ then _ else _ end}> |- _ => tt H
  | H : keywords <{while _ do _ end      }> |- _ => tt H
  | H : keywords <{var _                 }> |- _ => clear H
  | H : keywords <{fn _ _ _              }> |- _ => tt H
  | H : keywords <{call _ _              }> |- _ => tt H
  | H : keywords <{&_ : _                }> |- _ => clear H
  | H : keywords <{new _ : _             }> |- _ => tt H
  | H : keywords <{init _ _ : _          }> |- _ => tt H
  | H : keywords <{* _                   }> |- _ => tt H
  | H : keywords <{_ := _                }> |- _ => tt H
  | H : keywords <{acq _ _ _             }> |- _ => tt H
  | H : keywords <{cr _ _                }> |- _ => tt H
  | H : keywords <{wait _                }> |- _ => tt H
  | H : keywords <{reacq _               }> |- _ => clear H
  | H : keywords <{spawn _               }> |- _ => tt H
  end.

Ltac inv_kw  := _kw inv.
Ltac invc_kw := _kw invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma kw_init_term : forall t1 t2 ad' t',
  keywords t1                ->
  t1 --[e_init ad' t']--> t2 ->
  keywords t'.
Proof.
  intros. ind_tstep; invc_kw; auto.
Qed.

Lemma kw_write_term : forall t1 t2 ad' t',
  keywords t1                 ->
  t1 --[e_write ad' t']--> t2 ->
  keywords t'.
Proof.
  intros. ind_tstep; invc_kw; auto.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma kw_subst : forall x tx t,
  keywords t  ->
  keywords tx ->
  keywords <{[x := tx] t}>.
Proof.
  intros. induction t; invc_kw;
  simpl; repeat destruct _str_eq_dec; auto using keywords.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_kw_preservation :=
  intros; ind_tstep; repeat invc_kw; repeat constructor;
  auto using kw_subst, keywords, value.

Lemma kw_preservation_none : forall t1 t2,
  keywords t1    ->
  t1 --[e_none]--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_alloc : forall t1 t2 ad' T',
  keywords t1                 ->
  t1 --[e_alloc ad' T']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_init : forall t1 t2 ad' t',
  keywords t1                ->
  t1 --[e_init ad' t']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_read : forall t1 t2 ad' t',
  value t'    ->
  keywords t' ->
  (* --- *)
  keywords t1                ->
  t1 --[e_read ad' t']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_write : forall t1 t2 ad' t',
  keywords t1                 ->
  t1 --[e_write ad' t']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_acq : forall t1 t2 ad' t',
  value t'    ->
  keywords t' ->
  (* --- *)
  keywords t1               ->
  t1 --[e_acq ad' t']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_rel : forall t1 t2 ad',
  keywords t1            ->
  t1 --[e_rel ad']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_wacq : forall t1 t2 ad',
  keywords t1             ->
  t1 --[e_wacq ad']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_wrel : forall t1 t2 ad',
  keywords t1             ->
  t1 --[e_wrel ad']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_spawn : forall t1 t2 t',
  keywords t1             ->
  t1 --[e_spawn t']--> t2 ->
  keywords t2.
Proof. solve_kw_preservation. Qed.

Lemma kw_preservation_spawned : forall t1 t2 t',
  keywords t1             ->
  t1 --[e_spawn t']--> t2 ->
  keywords t'.
Proof. solve_kw_preservation. Qed.

(* ------------------------------------------------------------------------- *)

Corollary kw_preservation_memory : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   keywords      ->
  forall_threads ths1 keywords      ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_memory  m2   keywords.
Proof.
  intros. invc_cstep; try invc_mstep; trivial; intros ? ? ?;
  upsilon; eauto using kw_init_term, kw_write_term.
  omicron; upsilon; auto; eauto.
Qed.

Corollary kw_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   value ->
  (* --- *)
  forall_memory  m1   keywords      ->
  forall_threads ths1 keywords      ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_threads ths2 keywords. 
Proof.
  intros. invc_cstep; try invc_mstep; upsilon.
  - eauto using kw_preservation_none.
  - eauto using kw_preservation_alloc.
  - eauto using kw_preservation_init.
  - eauto using kw_preservation_read.
  - eauto using kw_preservation_write.
  - eauto using kw_preservation_acq.
  - eauto using kw_preservation_rel.
  - eauto using kw_preservation_wacq.
  - eauto using kw_preservation_wrel.
  - eauto using kw_preservation_spawn.
  - eauto using kw_preservation_spawned.
Qed.

Theorem kw_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1      value ->
  (* --- *)
  forall_program m1 ths1 keywords   ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  forall_program m2 ths2 keywords.
Proof.
  intros * ? [? ?] ?. split;
  eauto using kw_preservation_memory, kw_preservation_threads.
Qed.

Theorem kw_preservation_base : forall t,
  keywords t ->
  (* --- *)
  forall_program nil (base t) keywords.
Proof.
  auto using forallprogram_base, keywords.
Qed.

