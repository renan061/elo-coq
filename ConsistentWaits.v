From Elo Require Import Core.

From Elo Require Import NoCR.
From Elo Require Import NoReacq.
From Elo Require Import Keywords.

(* ------------------------------------------------------------------------- *)
(* consistent-waits                                                          *)
(* ------------------------------------------------------------------------- *)

Inductive wait_region : Set :=
  | WR_none
  | WR_self
  | WR_ad : addr -> wait_region
  .

(*
  (!!!) consistent_waits is an initial condition.
  (!!!) consistent_waits is an invariant.

  - WR_none  => no  immediate* wait/reacq.
  - WR_self  => any immediate* wait is a SELF wait; no immediate* reacq.
  - WR_ad ad => any immediate* wait/reacq has the given address.
  (waits/reacqs are immediate if they do not appear in fun/acq/cr/spawn blocks.)

  - fun   blocks are WR_none.
  - acq   blocks are WR_self.
  - cr ad blocks are (WR_ad ad).
  - spawn blocks are WR_none.
*)
Inductive consistent_waits: wait_region -> tm -> Prop :=
  | cw_unit  : forall WR,          consistent_waits WR <{unit              }>
  | cw_nat   : forall WR n,        consistent_waits WR <{nat n             }>
  | cw_plus  : forall WR t1 t2,    consistent_waits WR t1 ->
                                   consistent_waits WR t2 ->
                                   consistent_waits WR <{t1 + t2           }>
  | cw_monus : forall WR t1 t2,    consistent_waits WR t1 ->
                                   consistent_waits WR t2 ->
                                   consistent_waits WR <{t1 - t2           }>
  | cw_seq   : forall WR t1 t2,    consistent_waits WR t1 ->
                                   consistent_waits WR t2 ->
                                   consistent_waits WR <{t1; t2            }>
  | cw_if    : forall WR t1 t2 t3, consistent_waits WR t1 ->
                                   consistent_waits WR t2 ->
                                   consistent_waits WR t3 ->
                                   consistent_waits WR (tm_if t1 t2 t3     )
  | cw_while : forall WR t1 t2,    consistent_waits WR t1 ->
                                   consistent_waits WR t2 ->
                                   consistent_waits WR <{while t1 do t2 end}>
  | cw_var   : forall WR x,        consistent_waits WR <{var x             }>
  | cw_fun   : forall WR x Tx t,   consistent_waits WR_none t  ->
                                   consistent_waits WR <{fn x Tx t         }>
  | cw_call  : forall WR t1 t2,    consistent_waits WR t1 ->
                                   consistent_waits WR t2 ->
                                   consistent_waits WR <{call t1 t2        }>
  | cw_ref   : forall WR ad T,     consistent_waits WR <{&ad : T           }>
  | cw_new   : forall WR t T,      consistent_waits WR t  ->
                                   consistent_waits WR <{new t : T         }>
  | cw_init  : forall WR ad t T,   consistent_waits WR t  ->
                                   consistent_waits WR <{init ad t : T     }>
  | cw_load  : forall WR t,        consistent_waits WR t  ->
                                   consistent_waits WR <{*t                }>
  | cw_asg   : forall WR t1 t2,    consistent_waits WR t1 ->
                                   consistent_waits WR t2 ->
                                   consistent_waits WR <{t1 := t2          }>
  | cw_acq   : forall WR t1 x t2,  consistent_waits WR t1        ->
                                   consistent_waits (WR_self) t2 ->
                                   consistent_waits WR <{acq t1 x t2       }>
  | cw_cr    : forall WR ad t,     consistent_waits (WR_ad ad) t ->
                                   consistent_waits WR <{cr ad t           }>

  | cw_wait1 :                   consistent_waits WR_self    <{wait (var SELF)}>
  | cw_wait2 : forall ad T,      consistent_waits (WR_ad ad) <{wait (&ad : T) }>
  | cw_reacq : forall ad,        consistent_waits (WR_ad ad) <{reacq ad       }>

  | cw_spawn : forall WR t,        consistent_waits WR_none t ->
                                   consistent_waits WR <{spawn t           }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _cw tt :=
  match goal with
  | H : consistent_waits _ <{unit                  }> |- _ => clear H
  | H : consistent_waits _ <{nat _                 }> |- _ => clear H
  | H : consistent_waits _ <{_ + _                 }> |- _ => tt H
  | H : consistent_waits _ <{_ - _                 }> |- _ => tt H
  | H : consistent_waits _ <{_; _                  }> |- _ => tt H
  | H : consistent_waits _ <{if _ then _ else _ end}> |- _ => tt H
  | H : consistent_waits _ <{while _ do _ end      }> |- _ => tt H
  | H : consistent_waits _ <{var _                 }> |- _ => clear H
  | H : consistent_waits _ <{fn _ _ _              }> |- _ => tt H
  | H : consistent_waits _ <{call _ _              }> |- _ => tt H
  | H : consistent_waits _ <{&_ : _                }> |- _ => clear H
  | H : consistent_waits _ <{new _ : _             }> |- _ => tt H
  | H : consistent_waits _ <{init _ _ : _          }> |- _ => tt H
  | H : consistent_waits _ <{* _                   }> |- _ => tt H
  | H : consistent_waits _ <{_ := _                }> |- _ => tt H
  | H : consistent_waits _ <{acq _ _ _             }> |- _ => tt H
  | H : consistent_waits _ <{cr _ _                }> |- _ => tt H
  | H : consistent_waits _ <{wait _                }> |- _ => tt H
  | H : consistent_waits _ <{reacq _               }> |- _ => tt H
  | H : consistent_waits _ <{spawn _               }> |- _ => tt H
  end.

Ltac inv_cw  := _cw inv.
Ltac invc_cw := _cw invc.

(* lemmas ------------------------------------------------------------------ *)

Lemma wrself_from_wrnone : forall t,
  consistent_waits WR_none t ->
  consistent_waits WR_self t.
Proof.
  intros. induction t; invc_cw; auto using consistent_waits. 
Qed.

Lemma wrad_from_wrnone : forall ad t,
  consistent_waits WR_none t ->
  consistent_waits (WR_ad ad) t.
Proof.
  intros. induction t; invc_cw; auto using consistent_waits. 
Qed.

Lemma wrnone_weakening : forall o t,
  value t ->
  (* --- *)
  consistent_waits o t ->
  consistent_waits WR_none t.
Proof.
  intros * Hval ?. invc Hval; invc_cw; auto using consistent_waits. 
Qed.

Lemma wrnone_strengthening : forall o t,
  consistent_waits WR_none t ->
  consistent_waits o t.
Proof.
  intros. induction t; invc_cw; auto using consistent_waits. 
Qed.

Lemma wrad_strengthening : forall o ad t,
  value t ->
  (* --- *)
  consistent_waits (WR_ad ad) t ->
  consistent_waits o t.
Proof.
  intros * Hval ?. invc Hval; invc_cw; auto using consistent_waits.
Qed.

Lemma wrnone_init_term : forall o t1 t2 ad' t',
  consistent_waits o t1 ->
  t1 --[e_init ad' t']--> t2   ->
  consistent_waits WR_none t'.
Proof.
  intros. gendep o; ind_tstep; intros; invc_cw;
  eauto using wrnone_weakening, consistent_waits.
Qed.

Lemma wrnone_write_term : forall o t1 t2 ad' t',
  consistent_waits o t1 ->
  t1 --[e_write ad' t']--> t2   ->
  consistent_waits WR_none t'.
Proof.
  intros. gendep o; ind_tstep; intros; invc_cw;
  eauto using wrnone_weakening, consistent_waits.
Qed.

(* important lemmas -------------------------------------------------------- *)

Local Lemma noreacq_from_nocr' : forall ad t wr,
  wr <> WR_ad ad        ->
  consistent_waits wr t ->
  (* --- *)
  no_cr    ad t ->
  no_reacq ad t.
Proof.
  intros ? ?. induction t; intros; invc_cw; invc_nocr; eauto using no_reacq;
  constructor; eauto;
  match goal with
  | IH : forall _, _ <> _ -> consistent_waits _ ?t -> _ -> no_reacq _ ?t
  , H  : consistent_waits ?wr ?t
  |- no_reacq _ ?t =>
      eapply (IH wr); eauto
  end;
  intros F; invc F. auto.
Qed.

Corollary noreacq_from_nocr1 : forall ad t,
  consistent_waits WR_none t ->
  (* --- *)
  no_cr    ad t ->
  no_reacq ad t.
Proof.
  intros. eapply noreacq_from_nocr'; eauto. intros F. invc F.
Qed.

Corollary noreacq_from_nocr2 : forall ad ad' t,
  consistent_waits (WR_ad ad') t ->
  ad <> ad'                      ->
  (* --- *)
  no_cr    ad t ->
  no_reacq ad t.
Proof.
  intros. eapply noreacq_from_nocr'; eauto. intros F. invc F. congruence.
Qed.

Local Lemma nocr_wacq_contradiction' : forall ad t1 t2 wr,
  wr <> WR_ad ad         ->
  consistent_waits wr t1 ->
  (* --- *)
  no_cr ad t1            ->
  t1 --[e_wacq ad]--> t2 ->
  False.
Proof.
  intros. gendep wr. ind_tstep; intros; invc_cw; invc_nocr; eauto.
  spec. spec.
  match goal with IH : _ -> _ -> _ -> False, H : consistent_waits ?wr _ |- _ =>
   eapply (IH wr); eauto
  end.
  intros F. invc F. auto.
Qed.

Corollary nocr_wacq_contradiction : forall ad t1 t2,
  consistent_waits WR_none t1 ->
  (* --- *)
  no_cr ad t1            ->
  t1 --[e_wacq ad]--> t2 ->
  False.
Proof.
  intros. eapply nocr_wacq_contradiction'; eauto. intros F. invc F.
Qed.

Local Lemma nocr_wrel_contradiction' : forall ad t1 t2 wr,
  wr <> WR_ad ad         ->
  consistent_waits wr t1 ->
  (* --- *)
  no_cr ad t1            ->
  t1 --[e_wrel ad]--> t2 ->
  False.
Proof.
  intros. gendep wr. ind_tstep; intros; invc_cw; invc_nocr; eauto.
  spec. spec.
  match goal with IH : _ -> _ -> _ -> False, H : consistent_waits ?wr _ |- _ =>
   eapply (IH wr); eauto
  end.
  intros F. invc F. auto.
Qed.

Corollary nocr_wrel_contradiction : forall ad t1 t2,
  consistent_waits WR_none t1 ->
  (* --- *)
  no_cr ad t1            ->
  t1 --[e_wrel ad]--> t2 ->
  False.
Proof.
  intros. eapply nocr_wrel_contradiction'; eauto. intros F. invc F.
Qed.

(* preservation lemmas ----------------------------------------------------- *)

Lemma wrnone_subst : forall x tx t,
  consistent_waits WR_none t  ->
  consistent_waits WR_none tx ->
  consistent_waits WR_none <{[x := tx] t}>
with wrself_subst : forall x tx t,
  x <> SELF ->
  consistent_waits WR_self t ->
  consistent_waits WR_none tx ->
  consistent_waits WR_self <{[x := tx] t}>
with wrad_subst  : forall ad x tx t,
  consistent_waits (WR_ad ad) t ->
  consistent_waits WR_none tx ->
  consistent_waits (WR_ad ad) <{[x := tx] t}>.
Proof.
  all: intros; induction t; invc_cw; simpl; repeat destruct _str_eq_dec;
       auto using wrself_from_wrnone, wrad_from_wrnone, consistent_waits.
Qed.

Lemma cw_subst : forall o x tx t,
  value tx ->
  (* --- *)
  x <> SELF             ->
  consistent_waits o t  ->
  consistent_waits o tx ->
  consistent_waits o <{[x := tx] t}>.
Proof.
  intros. gendep o. induction t; intros; inv_cw;
  simpl; repeat destruct _str_eq_dec; auto using consistent_waits;
  eauto using wrnone_weakening, consistent_waits, wrself_subst, wrad_subst.
Qed.

Lemma wrnone_subst_self : forall t ad T,
  consistent_waits WR_none t ->
  consistent_waits WR_none <{[SELF := (&ad : T)] t}>
with wrad_subst_self : forall t ad ad' T,
  consistent_waits (WR_ad ad') t ->
  consistent_waits (WR_ad ad') <{[SELF := (&ad : T)] t}>.
Proof.
  - intros. induction t; invc_cw;
    remember SELF as x; simpl; repeat destruct _str_eq_dec; subst;
    auto using consistent_waits.
  - intros. induction t; invc_cw;
    remember SELF as x; simpl; repeat destruct _str_eq_dec; subst;
    auto using consistent_waits.
Qed.

Lemma cw_subst_self : forall t ad T,
  consistent_waits WR_self t ->
  consistent_waits (WR_ad ad) <{[SELF := (&ad : T)] t}>.
Proof.
  intros. induction t; invc_cw;
  remember SELF as x; simpl; repeat destruct _str_eq_dec; subst;
  auto using wrnone_subst_self, wrad_subst_self, consistent_waits.
Qed.

(* preservation ------------------------------------------------------------ *)

Local Ltac solve_cw_preservation :=
  intros o **; gendep o; ind_tstep; intros;
  repeat invc_kw; repeat invc_cw; repeat constructor; auto;
  eauto using wrnone_strengthening, wrad_strengthening,
             cw_subst, cw_subst_self,
             consistent_waits.

Lemma cw_preservation_none : forall o t1 t2,
  keywords t1 ->
  (* --- *)
  consistent_waits o t1 ->
  t1 --[e_none]--> t2   ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_alloc : forall o t1 t2 ad' T',
  consistent_waits o t1       ->
  t1 --[e_alloc ad' T']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_init : forall o t1 t2 ad' t',
  consistent_waits o t1      ->
  t1 --[e_init ad' t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_read : forall o t1 t2 ad' t',
  value t'                    ->
  consistent_waits WR_none t' ->
  (* --- *)
  consistent_waits o t1      ->
  t1 --[e_read ad' t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_write : forall o t1 t2 ad' t',
  consistent_waits o t1       ->
  t1 --[e_write ad' t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_acq : forall o t1 t2 ad' t',
  value t'                    ->
  consistent_waits WR_none t' ->
  keywords t1                 ->
  (* --- *)
  consistent_waits o t1     ->
  t1 --[e_acq ad' t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_rel : forall o t1 t2 ad',
  consistent_waits o t1  ->
  t1 --[e_rel ad']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_wacq : forall o t1 t2 ad',
  consistent_waits o t1   ->
  t1 --[e_wacq ad']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_wrel : forall o t1 t2 ad',
  consistent_waits o t1   ->
  t1 --[e_wrel ad']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_spawn : forall o t1 t2 t',
  consistent_waits o t1   ->
  t1 --[e_spawn t']--> t2 ->
  consistent_waits o t2.
Proof. solve_cw_preservation. Qed.

Lemma cw_preservation_spawned : forall o t1 t2 t',
  consistent_waits o t1   ->
  t1 --[e_spawn t']--> t2 ->
  consistent_waits WR_none t'.
Proof. solve_cw_preservation. Qed.

(* ------------------------------------------------------------------------- *)

Corollary cw_preservation_memory : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   (consistent_waits WR_none) ->
  forall_threads ths1 (consistent_waits WR_none) ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2    ->
  forall_memory  m2   (consistent_waits WR_none).
Proof.
  intros. invc_cstep; try invc_mstep; trivial; intros ? ? ?;
  upsilon; eauto using wrnone_init_term, wrnone_write_term.
  omicron; upsilon; auto; eauto.
Qed.

Corollary cw_preservation_threads : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1   value    ->
  forall_threads ths1 keywords ->
  (* --- *)
  forall_memory  m1   (consistent_waits WR_none) ->
  forall_threads ths1 (consistent_waits WR_none) ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2              ->
  forall_threads ths2 (consistent_waits WR_none).
Proof.
  intros. invc_cstep; try invc_mstep; upsilon.
  - eauto using cw_preservation_none.
  - eauto using cw_preservation_alloc.
  - eauto using cw_preservation_init.
  - eauto using cw_preservation_read.
  - eauto using cw_preservation_write.
  - eauto using cw_preservation_acq.
  - eauto using cw_preservation_rel.
  - eauto using cw_preservation_wacq.
  - eauto using cw_preservation_wrel.
  - eauto using cw_preservation_spawn.
  - eauto using cw_preservation_spawned.
Qed.

Theorem cw_preservation_cstep : forall m1 m2 ths1 ths2 tid e,
  forall_memory  m1      value    ->
  forall_program m1 ths1 keywords ->
  (* --- *)
  forall_program m1 ths1 (consistent_waits WR_none) ->
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2                 ->
  forall_program m2 ths2 (consistent_waits WR_none).
Proof.
  intros * ? [_ ?] [? ?] ?. split;
  eauto using cw_preservation_memory, cw_preservation_threads.
Qed.

Theorem cw_preservation_base : forall t,
  consistent_waits WR_none t ->
  (* --- *)
  forall_program nil (base t) (consistent_waits WR_none).
Proof.
  auto using forallprogram_base, consistent_waits.
Qed.

