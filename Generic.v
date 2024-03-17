From Coq Require Import Lia.

From Elo Require Import Core.
From Elo Require Import Properties.

(* ------------------------------------------------------------------------- *)
(* meta-properties                                                           *)
(* ------------------------------------------------------------------------- *)

Section metaproperties.
  Variable P : mem -> tm -> Prop. 
  Variable m : mem.
  Variable t : tm.

  Definition mp_none t' :=
    P m t ->
    t --[EF_None]--> t' ->
    P m t'.

  Definition mp_alloc t' v T :=
    P m t ->
    t --[EF_Alloc (#m) v T]--> t' ->
    P (m +++ (v, T)) t'.

  Definition mp_read t' ad :=
    P m t ->
    t --[EF_Read ad m[ad].tm]--> t' ->
    P m t'.

  Definition mp_write t' ad v T :=
    P m t ->
    t --[EF_Write ad v T]--> t' ->
    P (m[ad <- (v, T)]) t'.

  Definition mp_spawn t' block :=
    P m t ->
    t --[EF_Spawn block]--> t' ->
    P m block.

  Definition mp_mem_add vT :=
    P m t ->
    P (m +++ vT) t.

  Definition mp_mem_set ad vT :=
    P m t ->
    P m[ad <- vT] t.

  Definition mp_mem_alloc t' v T :=
    forall_memory m (P m) ->
    t --[EF_Alloc (#m) v T]--> t' ->
    forall_memory (m +++ (v, T)) (P (m +++ (v, T))).

  Definition mp_mem_write t' ad v T :=
    forall_memory m (P m) ->
    t --[EF_Write ad v T]--> t' ->
    forall_memory m[ad <- (v, T)] (P m[ad <- (v, T)]).
End metaproperties.

(* ------------------------------------------------------------------------- *)
(* structural constructors                                                   *)
(* ------------------------------------------------------------------------- *)

Class Unit (P : mem -> tm -> Prop) := {
  Cunit : forall m, P m <{unit}>;
}.

Class New (P : mem -> tm -> Prop) := {
  Cnew : forall m t T, P m t           -> P m <{new T t}>;
  Dnew : forall m t T, P m <{new T t}> -> P m t;
}.

Class Load (P : mem -> tm -> Prop) := {
  Cload : forall m t, P m t      -> P m <{*t}>;
  Dload : forall m t, P m <{*t}> -> P m t;
}.

Class Asg (P : mem -> tm -> Prop) := {
  Casg : forall m t1 t2, P m t1 -> P m t2 -> P m <{t1 = t2}>;
  Dasg : forall m t1 t2, P m <{t1 = t2}>  -> P m t1 /\ P m t2;
}.

Class Fun (P : mem -> tm -> Prop) := {
  Cfun : forall m x T t, P m t            -> P m <{fn x T t}>;
  Dfun : forall m x T t, P m <{fn x T t}> -> P m t;
}.

Class Call (P : mem -> tm -> Prop) := {
  Ccall : forall m t1 t2, P m t1 -> P m t2   -> P m <{call t1 t2}>;
  Dcall : forall m t1 t2, P m <{call t1 t2}> -> P m t1 /\ P m t2;
}.

Class Seq (P : mem -> tm -> Prop) := {
  Cseq : forall m t1 t2, P m t1 -> P m t2 -> P m <{t1; t2}>;
  Dseq : forall m t1 t2, P m <{t1; t2}>   -> P m t1 /\ P m t2;
}.

Class Spawn (P : mem -> tm -> Prop) := {
  Cspawn : forall m t, P m t           -> P m <{spawn t}>;
  Dspawn : forall m t, P m <{spawn t}> -> P m t;
}.

(* ------------------------------------------------------------------------- *)
(* may constructors                                                          *)
(* ------------------------------------------------------------------------- *)

(* TODO *)
Class NeverSpawn (P : mem -> tm -> Prop) := {
  never_spawn : forall m t, ~ P m <{spawn t}>;
}.

Class MayAsg (P : mem -> tm -> Prop) := {
  Casg1 : forall m t1 t2, P m t1           -> P m <{t1 = t2}>;
  Casg2 : forall m t1 t2, P m t2           -> P m <{t1 = t2}>;
  DOasg : forall m t1 t2, P m <{t1 = t2}>  -> P m t1 \/ P m t2;
}.

Class MayCall (P : mem -> tm -> Prop) := {
  Ccall1 : forall m t1 t2, P m t1             -> P m <{call t1 t2}>;
  Ccall2 : forall m t1 t2, P m t2             -> P m <{call t1 t2}>;
  DOcall : forall m t1 t2, P m <{call t1 t2}> -> P m t1 \/ P m t2;
}.

Class MaySeq (P : mem -> tm -> Prop) := {
  Cseq1 : forall m t1 t2, P m t1         -> P m <{t1; t2}>;
  Cseq2 : forall m t1 t2, P m t2         -> P m <{t1; t2}>;
  DOseq : forall m t1 t2, P m <{t1; t2}> -> P m t1 \/ P m t2;
}.

(* ------------------------------------------------------------------------- *)
(* inv may-must                                                              *)
(* ------------------------------------------------------------------------- *)

Local Ltac eapply_or  tactic H := eapply tactic in H as [? | ?].
Local Ltac eapply_and tactic H := eapply tactic in H as [?   ?].

(* match inversion structural-may-must *)
Local Ltac match_inv_smm tactic :=
  match goal with
  (* structural & must *)
  | _ : New   ?P, H : ?P _ <{new _ _ }> |- _ => eapply Dnew   in H
  | _ : Load  ?P, H : ?P _ <{* _     }> |- _ => eapply Dload  in H
  | _ : Asg   ?P, H : ?P _ <{_ = _   }> |- _ => eapply Dasg   in H as [? ?]
  | _ : Fun   ?P, H : ?P _ <{fn _ _ _}> |- _ => eapply Dfun   in H
  | _ : Call  ?P, H : ?P _ <{call _ _}> |- _ => eapply Dcall  in H as [? ?]
  | _ : Seq   ?P, H : ?P _ <{_ ; _   }> |- _ => eapply Dseq   in H as [? ?]
  | _ : Spawn ?P, H : ?P _ <{spawn _ }> |- _ => eapply Dspawn in H
  (* may *)
  | _ : MayAsg  ?P, H : ?P _ <{_ = _   }> |- _ => eapply_or DOasg  H
  | _ : MayCall ?P, H : ?P _ <{call _ _}> |- _ => eapply_or DOcall H
  | _ : MaySeq  ?P, H : ?P _ <{_ ; _   }> |- _ => eapply_or DOseq  H
  end.

Ltac inv_smm  := match_inv_smm inv.
Ltac invc_smm := match_inv_smm invc.

(* ------------------------------------------------------------------------- *)
(* subst                                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma must_subst (P : mem -> tm -> Prop)
  `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m t tx x,
      P m t ->
      P m tx ->
      P m ([x := tx] t).
Proof.
  intros. induction t; trivial; simpl; try inv_smm;
  eauto using Cnew, Cload, Casg, Ccall, Cseq, Cspawn;
  destruct string_eq_dec; subst; eauto using Cfun.
Qed.

Lemma inv_may_not_asg (P : mem -> tm -> Prop) `{Hasg : MayAsg P} :
  forall m t1 t2,
    ~ P m <{ t1 = t2 }> ->
    ~ P m t1 /\ ~ P m t2.
Proof.
  intros * H. split; intros ?; eapply H.
  - eapply Hasg.(Casg1). assumption.
  - eapply Hasg.(Casg2). assumption.
Qed.

Lemma inv_struct_not_fun (P : mem -> tm -> Prop) `{Hfun : Fun P} :
  forall m t x T,
    ~ P m <{fn x T t}> ->
    ~ P m t.
Proof.
  intros * H. destruct Hfun. intros ?. eauto.
Qed.

Lemma may_subst (P : mem -> tm -> Prop)
  `{New        P}
  `{Load       P}
  `{MayAsg     P}
  `{Fun        P}
  `{MayCall    P}
  `{MaySeq     P}
  `{NeverSpawn P} :
    forall m t tx x,
      ~ P m t ->
      ~ P m tx ->
      ~ P m ([x := tx] t).
Proof.
  intros. intros F. induction t; simpl in *; eauto; try inv_smm;
  eauto using Cnew, Cload, Casg1, Casg2, Ccall1, Ccall2, Cseq1, Cseq2.
  - destruct string_eq_dec; subst; eauto.
  - destruct string_eq_dec; subst; eauto. inv_smm. eauto using Cfun.
  - contradict F. eauto using never_spawn.
Qed.

(* ------------------------------------------------------------------------- *)
(* must valid-addresses                                                      *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_vad :=
  constructor; intros;
  eauto using valid_addresses;
  inv_vad; try split; assumption.

#[export] Instance vad_must_unit  : Unit  valid_addresses. solve_vad. Qed.
#[export] Instance vad_must_new   : New   valid_addresses. solve_vad. Qed.
#[export] Instance vad_must_load  : Load  valid_addresses. solve_vad. Qed.
#[export] Instance vad_must_asg   : Asg   valid_addresses. solve_vad. Qed.
#[export] Instance vad_must_fun   : Fun   valid_addresses. solve_vad. Qed.
#[export] Instance vad_must_call  : Call  valid_addresses. solve_vad. Qed.
#[export] Instance vad_must_seq   : Seq   valid_addresses. solve_vad. Qed.
#[export] Instance vad_must_spawn : Spawn valid_addresses. solve_vad. Qed.

(* ------------------------------------------------------------------------- *)
(* must consistently-typed-references                                        *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_ctr :=
  constructor; intros;
  eauto using consistently_typed_references;
  inv_ctr; try split; assumption.

#[export] Instance ctr_must_unit  : Unit  consistently_typed_references.
Proof. solve_ctr. Qed.
#[export] Instance ctr_must_new   : New   consistently_typed_references.
Proof. solve_ctr. Qed.
#[export] Instance ctr_must_load  : Load  consistently_typed_references.
Proof. solve_ctr. Qed.
#[export] Instance ctr_must_asg   : Asg   consistently_typed_references.
Proof. solve_ctr. Qed.
#[export] Instance ctr_must_fun   : Fun   consistently_typed_references.
Proof. solve_ctr. Qed.
#[export] Instance ctr_must_call  : Call  consistently_typed_references.
Proof. solve_ctr. Qed.
#[export] Instance ctr_must_seq   : Seq   consistently_typed_references.
Proof. solve_ctr. Qed.
#[export] Instance ctr_must_spawn : Spawn consistently_typed_references.
Proof. solve_ctr. Qed. 

(* ------------------------------------------------------------------------- *)
(* may access                                                                *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_acc :=
  intros; constructor; intros; try (intros ?); eauto using access; inv_acc;
  solve [assumption | left; assumption | right; assumption].

#[export] Instance acc_struct_new  : forall ad, New        (access ad).
Proof. solve_acc. Qed.
#[export] Instance acc_struct_load : forall ad, Load       (access ad).
Proof. solve_acc. Qed.
#[export] Instance acc_may_asg     : forall ad, MayAsg     (access ad).
Proof. solve_acc. Qed.
#[export] Instance acc_struct_fun  : forall ad, Fun        (access ad).
Proof. solve_acc. Qed.
#[export] Instance acc_may_call    : forall ad, MayCall    (access ad).
Proof. solve_acc. Qed.
#[export] Instance acc_may_seq     : forall ad, MaySeq     (access ad).
Proof. solve_acc. Qed.
#[export] Instance acc_never_spawn : forall ad, NeverSpawn (access ad).
Proof. solve_acc. Qed.

(* ------------------------------------------------------------------------- *)
(* may unsafe-access                                                         *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_uacc :=
  intros; constructor; intros; try (intros ?); eauto using unsafe_access;
  inv_uacc; solve [assumption | left; assumption | right; assumption].

#[export] Instance uacc_struct_new  : forall ad, New        (unsafe_access ad).
Proof. solve_uacc. Qed.
#[export] Instance uacc_struct_load : forall ad, Load       (unsafe_access ad).
Proof. solve_uacc. Qed.
#[export] Instance uacc_may_asg     : forall ad, MayAsg     (unsafe_access ad).
Proof. solve_uacc. Qed.
#[export] Instance uacc_struct_fun  : forall ad, Fun        (unsafe_access ad).
Proof. solve_uacc. Qed.
#[export] Instance uacc_may_call    : forall ad, MayCall    (unsafe_access ad).
Proof. solve_uacc. Qed.
#[export] Instance uacc_may_seq     : forall ad, MaySeq     (unsafe_access ad).
Proof. solve_uacc. Qed.
#[export] Instance uacc_never_spawn : forall ad, NeverSpawn (unsafe_access ad).
Proof. solve_uacc. Qed.

(* ------------------------------------------------------------------------- *)
(* must no-mut                                                               *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_nomut :=
  constructor; intros;
  eauto using no_mut;
  inv_nomut; try split; assumption.

#[export] Instance nomut_must_new   : New   (fun m t => no_mut t).
Proof. solve_nomut. Qed.
#[export] Instance nomut_must_load  : Load  (fun m t => no_mut t).
Proof. solve_nomut. Qed.
#[export] Instance nomut_must_asg   : Asg   (fun m t => no_mut t).
Proof. solve_nomut. Qed.
#[export] Instance nomut_must_fun   : Fun   (fun m t => no_mut t).
Proof. solve_nomut. Qed.
#[export] Instance nomut_must_call  : Call  (fun m t => no_mut t).
Proof. solve_nomut. Qed.
#[export] Instance nomut_must_seq   : Seq   (fun m t => no_mut t).
Proof. solve_nomut. Qed.
#[export] Instance nomut_must_spawn : Spawn (fun m t => no_mut t).
Proof. solve_nomut. Qed.

(* ------------------------------------------------------------------------- *)
(* must safe-spawns                                                          *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_ss :=
  constructor; intros;
  eauto using safe_spawns;
  inv_ss; try split; assumption.

#[export] Instance ss_must_new   : New  (fun _ t => safe_spawns t).
Proof. solve_ss. Qed.
#[export] Instance ss_must_load  : Load (fun _ t => safe_spawns t).
Proof. solve_ss. Qed.
#[export] Instance ss_must_asg   : Asg  (fun _ t => safe_spawns t).
Proof. solve_ss. Qed.
#[export] Instance ss_must_fun   : Fun  (fun _ t => safe_spawns t).
Proof. solve_ss. Qed.
#[export] Instance ss_must_call  : Call (fun _ t => safe_spawns t).
Proof. solve_ss. Qed.
#[export] Instance ss_must_seq   : Seq  (fun _ t => safe_spawns t).
Proof. solve_ss. Qed.

(* ------------------------------------------------------------------------- *)
(* generic preservation                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma tstep_spawn_preservation (P : mem -> tm -> Prop) 
  `{Unit P} `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m t t' block,
      P m t ->
      t --[EF_Spawn block]--> t' ->
      P m t'.
Proof.
  intros. induction_tstep; inv_smm;
  eauto using Cunit, Cnew, Cload, Casg, Ccall, Cseq.
Qed.

Lemma cstep_preservation (P : mem -> tm -> Prop)
  `{Unit P} `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m m' ths ths' tid e,
      (forall t,        mp_none  P m ths[tid] t)        ->
      (forall t v T,    mp_alloc P m ths[tid] t v T)    ->
      (forall t ad,     mp_read  P m ths[tid] t ad)     ->
      (forall t ad v T, mp_write P m ths[tid] t ad v T) ->
      (forall t block,  mp_spawn P m ths[tid] t block)  ->
      (* Untouched -- Alloc *)
      (forall tid' t ad v T,
        P m ths[tid'] ->
        ths[tid] --[EF_Alloc ad v T]--> t ->
        P (m +++ (v, T)) ths[tid']
      ) ->
      (* Untouched -- Write *)
      (forall tid' t ad v T,
        ad < #m ->
        forall_threads ths (P m) ->
        ths[tid] --[EF_Write ad v T]--> t ->
        P m[ad <- (v, T)] ths[tid']
      ) ->
      (* What we want to prove: *)
      forall_memory m (P m) ->
      forall_threads ths (P m) ->
      m / ths ~~[tid, e]~~> m' / ths' ->
      forall_threads ths' (P m').
Proof.
  intros * ? ? ? ? ? ? ? ? Hths ? tid'.
  inv_cstep.
  - (* C-Spawn *)
    decompose sum (lt_eq_lt_dec tid' (#ths)); subst;
    simpl_array; unfold mp_spawn in *; eauto using Cunit.
    destruct (nat_eq_dec tid tid'); subst; simpl_array; eauto.
    eapply (tstep_spawn_preservation P _ _ t' block (Hths tid')); eauto.
  - (* C-Mem *)
    destruct (lt_eq_lt_dec tid' (#ths)) as [[? | ?] | Hgt]; subst; try lia.
    + destruct (nat_eq_dec tid tid'); subst; simpl_array;
      inv_mstep; unfold mp_none, mp_alloc, mp_read, mp_write in *; eauto.
    + simpl_array. eauto using Cunit.
    + rewrite <- (set_preserves_length _ tid t') in Hgt.
      simpl_array. eauto using Cunit.
Qed.

Lemma memoryless_cstep_preservation (P : tm -> Prop) :
  forall m m' ths ths' tid e,
    (* tstep_spawn_preservation *)
    (forall t t' block,
      P t ->
      t --[EF_Spawn block]--> t' ->
      P t') ->
    (* mstep_preservation *)
    (forall t',
      P ths[tid] ->
      m / ths[tid] ==[e]==> m' / t' ->
      P t') ->
    (* spawn_block *)
    (forall t t' block,
      P t ->
      t --[EF_Spawn block]--> t' ->
      P block) ->
   (* What we want to prove: *)
    forall_threads ths P ->
    m / ths ~~[tid, e]~~> m' / ths' ->
    forall_threads ths' P.
Proof.
  intros * Hspawn Hmstep Hblock Hp Hcstep tid'. inv_cstep.
  - (* C-Spawn *)
    destruct (lt_eq_lt_dec tid' (#ths)) as [[? | ?] | Hb]; subst; try lia.
    + (* tid' < #ths *)
      destruct (nat_eq_dec tid tid'); subst; simpl_array.
      * (* tid' == tid =====> P t'             *)
        eapply (Hspawn _ t' block (Hp tid')). assumption.
      * (* tid' != tid =====> P ths[tid']      *)
        eapply Hp.
    + (* tid' = #ths    =====> P block          *)
      rewrite <- (set_preserves_length _ tid t'). simpl_array.
      eapply (Hblock _ t' _ (Hp tid)). assumption.
    + (* tid' > #ths    =====> P thread_default *)
      rewrite <- (set_preserves_length _ tid t') in Hb. specialize (Hp (#ths)).
      simpl_array. exact Hp.
  - (* C-Mem *)
    destruct (nat_eq_dec tid tid'); subst; simpl_array.
      * (* tid == tid' =====> P t'             *)
        eapply (Hmstep t' (Hp tid')). assumption.
      * (* tid != tid' =====> P ths[tid']      *)
        eapply Hp.
Qed.

Lemma tstep_alloc_value (P : mem -> tm -> Prop) 
  `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m t t' ad v T,
      P m t ->
      t --[EF_Alloc ad v T]--> t' ->
      P m v.
Proof.
  intros. induction_tstep; inv_smm; eauto.
Qed.

Lemma tstep_write_value (P : mem -> tm -> Prop) 
  `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m t t' ad v T,
      P m t ->
      t --[EF_Write ad v T]--> t' ->
      P m v.
Proof.
  intros. induction_tstep; inv_smm; eauto.
Qed.

Lemma tstep_spawn_block (P : mem -> tm -> Prop) 
  `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m t t' block,
      P m t ->
      t --[EF_Spawn block]--> t' ->
      P m block.
Proof.
  intros. induction_tstep; inv_smm; eauto.
Qed.

Local Lemma tstep_alloc_mem_preservation (P : mem -> tm -> Prop) 
  `{Unit P} `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m t t' v T,
      (forall ad, mp_mem_add P m m[ad].tm (v, T)) ->
      mp_mem_add P m t (v, T) ->
      P m t ->
      forall_memory m (P m) ->
      t --[EF_Alloc (#m) v T]--> t' ->
      forall_memory (m +++ (v, T)) (P (m +++ (v, T))).
Proof.
  unfold mp_mem_add.
  intros ** ad. decompose sum (lt_eq_lt_dec ad (#m)); subst; simpl_array;
  eauto using (tstep_alloc_value P), Cunit.
Qed.

Local Lemma tstep_write_mem_preservation (P : mem -> tm -> Prop) 
  `{Unit P} `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m t t' ad v T,
      mp_mem_set P m t ad (v, T) ->
      (forall ad', mp_mem_set P m m[ad'].tm ad (v, T)) ->
      ad < #m ->
      P m t ->
      forall_memory m (P m) ->
      t --[EF_Write ad v T]--> t' ->
      forall_memory m[ad <- (v, T)] (P m[ad <- (v, T)]).
Proof.
  intros ** ad'.
  destruct (nat_eq_dec ad ad'); subst; simpl_array;
  unfold mp_mem_set in *; eauto using (tstep_write_value P).
Qed.

Corollary cstep_mem_preservation (P : mem -> tm -> Prop) 
  `{Unit P} `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m m' ths ths' tid e,
      (forall v T, mp_mem_add P m ths[tid] (v, T)) ->
      (forall ad v T, mp_mem_add P m m[ad].tm (v, T)) ->
      (forall ad v T, mp_mem_set P m ths[tid] ad (v, T)) ->
      (forall ad ad' v T, mp_mem_set P m m[ad'].tm ad (v, T)) ->
      forall_threads ths (P m) ->
      (* --- *)
      forall_memory m (P m) ->
      m / ths ~~[tid, e]~~> m' / ths' ->
      forall_memory m' (P m').
Proof.
  intros. inv_cstep; trivial. inv_mstep;
  eauto using tstep_alloc_mem_preservation, tstep_write_mem_preservation.
Qed.

Corollary cstep_mem_preservation' (P : mem -> tm -> Prop) 
  `{Unit P} `{New P} `{Load P} `{Asg P} `{Fun P} `{Call P} `{Seq P} `{Spawn P} :
    forall m m' ths ths' tid e,
      (forall t' v T, mp_mem_alloc P m ths[tid] t' v T)       ->
      (forall t' ad v T, mp_mem_write P m ths[tid] t' ad v T) ->
      forall_threads ths (P m) ->
      (* --- *)
      forall_memory m (P m) ->
      m / ths ~~[tid, e]~~> m' / ths' ->
      forall_memory m' (P m').
Proof.
  unfold mp_mem_alloc, mp_mem_write.  
  intros. inv_cstep; trivial. inv_mstep; eauto.
Qed.
