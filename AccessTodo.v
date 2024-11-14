






























(* ------------------------------------------------------------------------- *)
(* access-promise-1                                                          *)
(* ------------------------------------------------------------------------- *)

Definition access_promise1 (ad : addr) (m : mem) (t : tm) :=  forall adx T,
  m[ad].T = `w&T` ->
  xaccess adx ad m t ->
  access ad m t ->
  False.

(* constructors ------------------------------------------------------------ *)

Local Lemma ap1_unit : forall ad m,
  access_promise1 ad m <{unit}>.
Proof.
  intros until 3. invc_xacc.
Qed.

Local Lemma ap1_nat : forall ad m n,
  access_promise1 ad m <{nat n}>.
Proof.
  intros until 3. invc_xacc.
Qed.

Local Lemma ap1_ref : forall ad m n,
  access_promise1 ad m <{nat n}>.
Proof.
  intros until 3. invc_xacc.
Qed.

Local Lemma ap1_var : forall ad m x,
  access_promise1 ad m <{var x}>.
Proof.
  intros until 3. invc_xacc.
Qed.

Local Lemma ap1_fun : forall ad m x Tx t,
  access_promise1 ad m t -> access_promise1 ad m <{fn x Tx t}>.
Proof.
  intros until 4. invc_acc; invc_xacc. eauto.
Qed.

Local Lemma ap1_call : forall ad m t1 t2,
  access_promise1 ad m t1 ->
  access_promise1 ad m t2 ->
  access_promise1 ad m <{call t1 t2}>.
Proof.
  intros. intros until 3. invc_acc; invc_xacc; eauto.
Abort.

#[export] Hint Resolve
  ap1_unit  ap1_nat
  ap1_var   ap1_fun
  ap1_ref
  : ap1.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_ap1 :=
  intros; try split; intros until 3; eauto using access, xaccess. 

Local Lemma inv_ap1_fun : forall ad m x Tx t,
  access_promise1 ad m <{fn x Tx t}> ->
  access_promise1 ad m t.
Proof. solve_inv_ap1. Qed.

Local Lemma inv_ap1_call : forall ad m t1 t2,
  access_promise1 ad m <{call t1 t2}> ->
  access_promise1 ad m t1 /\ access_promise1 ad m t2.
Proof. solve_inv_ap1. Qed.

Ltac dup_apply1 H L := specialize H as H'; eapply L in H.
Ltac dup_apply2 H L := specialize H as H'; eapply L in H as [? ?].

Ltac inv_ap1 :=
  match goal with
  | H : access_promise1 _ _ <{fn _ _ _   }> |- _ => dup_apply1 H inv_ap1_fun
  | H : access_promise1 _ _ <{call _ _   }> |- _ => dup_apply2 H inv_ap1_call
  end.

(* preservation ------------------------------------------------------------ *)

Local Lemma acc_subst_backwards : forall ad m x tx t,
  access ad m <{[x := tx] t}> ->
  access ad m tx \/ access ad m t.
Proof.
  intros. induction t; eauto; simpl in *; try destruct str_eq_dec; eauto;
  invc_acc; aspecialize;
  match goal with H : _ \/ _ |- _ => destruct H end;
  eauto using access.
Qed.

Local Lemma xacc_subst_backwards : forall adx ad m x tx t,
  xaccess adx ad m <{ [x := tx] t }> ->
  (access ad m tx \/ xaccess adx ad m tx \/ xaccess adx ad m t).
Proof.
  intros. induction t; eauto; simpl in *; try destruct str_eq_dec; eauto;
  inv_xacc; try aspecialize;
  try solve [
    match goal with H : _ \/ _ \/ _ |- _ => decompose sum H end;
    eauto using access, xaccess
  ].
  eapply acc_subst_backwards in H1 as [? | ?];
  eauto using xaccess.
Qed.

Local Lemma ap1_subst : forall ad m x tx Tx t,
  valid_crs <{call (fn x Tx t) tx}> ->
  value tx ->
  access_promise1 ad m <{call (fn x Tx t) tx}> ->
  access_promise1 ad m t ->
  access_promise1 ad m tx ->
  access_promise1 ad m <{[x := tx] t}>.
Proof.
  intros * Hvcrs Hval H Ht Htx. intros until 3.
  repeat invc_vcrs.
eapply value_then_nocrs in H6; trivial.
  specialize (Ht adx T H0).
  specialize (Htx adx T H0).
  assert (Hacc : access ad m tx \/ access ad m t)
    by eauto using acc_subst_backwards.
  assert (Hxacc : access ad m tx \/ xaccess adx ad m tx \/ xaccess adx ad m t)
    by eauto using xacc_subst_backwards.
  destruct Hacc as [? | ?]; destruct Hxacc as [? | [? | ?]]; repeat aspecialize;
  eauto using access, xaccess.
  - Usar o tipo. admit.
  - admit.
Abort.

Local Lemma ap1_preservation_none : forall ad m t1 t2,
  access_promise1 ad m t1 ->
  t1 --[e_none]--> t2 ->
  access_promise1 ad m t2.
Proof.
  intros * Hap ?. ind_tstep; repeat clean.
  - inv_ap1. repeat aspecialize. intros until 3.
    invc_xacc; invc_acc; eauto.
    + assert (xaccess adx ad m t1) by admit.
      eauto using access, xaccess.
    + assert (access ad m t1) by admit.
      eauto using access, xaccess.
  - admit.
  - inv_ap1. eapply inv_ap1_fun in H0 as ?.




    intros until 3; eauto using access, xaccess.
  - intros until 2.
Qed.

Local Lemma ap1_preservation_mstep : forall m1 m2 ths tid t e,
  xacc_acc_promise m1 ths ->
  m1 / ths[tid] ==[e]==> m2 / t ->
  xacc_acc_promise m2 ths[tid <- t].
Proof.
  intros. invc_mstep.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.
















(* ------------------------------------------------------------------------- *)
(* guards                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition guards adx ad m :=
  exists T, m[adx].T = `x&T` /\ access ad m m[adx].t.

(* ------------------------------------------------------------------------- *)
(* guard-promise                                                             *)
(* ------------------------------------------------------------------------- *)

Definition guard_promise (m : mem) (t : tm) := forall adx ad T,
  m[ad].T = `w&T` ->
  guards adx ad m ->
  ~ access ad m t.

Local Ltac solve_cons_gp :=
  intros ** ? ? ? ? ?; eauto with not_access.

Lemma gp_unit : forall m,
  guard_promise m <{unit}>.
Proof. solve_cons_gp. Qed.

Lemma gp_nat : forall m n,
  guard_promise m <{nat n}>.
Proof. solve_cons_gp. Qed.

Lemma gp_var : forall m x,
  guard_promise m <{var x}>.
Proof. solve_cons_gp. Qed.

Lemma gp_fun : forall m x Tx t,
  guard_promise m t -> guard_promise m <{fn x Tx t}>.
Proof. solve_cons_gp. Qed.

Lemma gp_call : forall m t1 t2,
  guard_promise m t1 -> guard_promise m t2 -> guard_promise m <{call t1 t2}>.
Proof. solve_cons_gp. Qed.

(* gp_ref *)

Lemma gp_new : forall m t T,
  guard_promise m t -> guard_promise m <{new t : T}>.
Proof. solve_cons_gp. Qed.

Lemma gp_load : forall m t,
  guard_promise m t -> guard_promise m <{*t}>.
Proof. solve_cons_gp. Qed.

Lemma gp_asg : forall m t1 t2,
  guard_promise m t1 -> guard_promise m t2 -> guard_promise m <{t1 := t2}>.
Proof. solve_cons_gp. Qed.

Lemma gp_acq : forall m t1 t2,
  guard_promise m t1 -> guard_promise m t2 -> guard_promise m <{acq t1 t2}>.
Proof. solve_cons_gp. Qed.

Lemma gp_cr : forall m adx t,
  guard_promise m <{cr adx t}>.
Proof. solve_cons_gp. Qed.

Lemma gp_spawn : forall m t,
  guard_promise m <{spawn t}>.
Proof. solve_cons_gp. Qed.

#[export] Hint Resolve
  gp_unit gp_nat
  gp_var  gp_fun gp_call
  gp_new  gp_load gp_asg
  gp_acq  gp_cr
  gp_spawn
  : guard_promise.

(* inversion --------------------------------------------------------------- *)

Local Ltac solve_inv_gp :=
  intros * H; try split; intros ? ? ? Had Hguards ?;
  eapply H; eauto using access.

Local Lemma inv_gp_fun : forall m x Tx t,
  guard_promise m <{fn x Tx t}> -> guard_promise m t.
Proof. solve_inv_gp. Qed. 

Local Lemma inv_gp_call : forall m t1 t2,
  guard_promise m <{call t1 t2}> -> guard_promise m t1 /\ guard_promise m t2.
Proof. solve_inv_gp. Qed. 

Local Lemma inv_gp_new : forall m t T,
  guard_promise m <{new t : T}> -> guard_promise m t.
Proof. solve_inv_gp. Qed.

Local Lemma inv_gp_load : forall m t,
  guard_promise m <{*t}> -> guard_promise m t.
Proof. solve_inv_gp. Qed.

Local Lemma inv_gp_asg : forall m t1 t2,
  guard_promise m <{t1 := t2}> -> guard_promise m t1 /\ guard_promise m t2.
Proof. solve_inv_gp. Qed.

Local Lemma inv_gp_acq : forall m t1 t2,
  guard_promise m <{acq t1 t2}> -> guard_promise m t1 /\ guard_promise m t2.
Proof. solve_inv_gp. Qed.

Ltac invc_gp :=
  match goal with
  | H : guard_promise _ <{unit     }> |- _ => clear H
  | H : guard_promise _ <{nat _    }> |- _ => clear H
  | H : guard_promise _ <{var _    }> |- _ => clear H
  | H : guard_promise _ <{fn _ _ _ }> |- _ => eapply inv_gp_fun    in H
  | H : guard_promise _ <{call _ _ }> |- _ => eapply inv_gp_call   in H as [? ?]
  | H : guard_promise _ <{& _ : _  }> |- _ => idtac H (* TODO *)
  | H : guard_promise _ <{new _ : _}> |- _ => eapply inv_gp_new    in H
  | H : guard_promise _ <{* _      }> |- _ => eapply inv_gp_load   in H
  | H : guard_promise _ <{_ := _   }> |- _ => eapply inv_gp_asg    in H as [? ?]
  | H : guard_promise _ <{acq _ _  }> |- _ => eapply inv_gp_acq    in H as [? ?]
  | H : guard_promise _ <{cr _ _   }> |- _ => clear H
  | H : guard_promise _ <{spawn _  }> |- _ => clear H
  end.

(* lemmas ------------------------------------------------------------------ *)

Lemma gp_tstep_write_term : forall m t1 t2 ad t T,
  guard_promise m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  guard_promise m t.
Proof.
  intros. ind_tstep; try solve [invc_gp; eauto with guard_promise].
  repeat clean.
Abort.

(* preservation lemmas ----------------------------------------------------- *)

Local Lemma acc_mem_set_X_backwards : forall m t ad ad' X,
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad m[ad'.X <- X] t ->
  access ad m t.
Proof.
  intros * ? ? Hacc. induction Hacc; invc_vr; eauto using access;
  omicron; eauto using access.
Qed.

Local Lemma acc_mem_set_tT_backwards1 : forall m t ad ad' t' T',
  ~ access ad m t' ->
  (* --- *)
  access ad m[ad'.tT <- t' T'] t ->
  access ad m t.
Proof.
  intros * ? Hacc. remember (m[ad'.tT <- t' T']) as m'.
  induction Hacc; inv Heqm'; eauto using access;
  match goal with |- access _ _ <{& ?ad : _}> => rename ad into ad'' end;
  destruct (nat_eq_dec ad' ad''); subst; try (sigma; eauto using access);
  destruct (nat_eq_dec ad'' ad); subst; eauto using access;
  rewrite (set_get_eq cell_default) in IHHacc; try contradiction;
  omicron; eauto; inv_acc.
Qed.

Lemma acc_mem_set_tT_backwards2 : forall m t ad ad' c,
  ~ access ad' m t ->
  (* --- *)
  access ad m[ad' <- c] t ->
  access ad m t.
Proof.
  intros * ? Hacc. induction Hacc; invc_nacc; eauto using access;
  sigma; eauto using access.
Qed.

Local Lemma gp_mem_set_X : forall m t ad X,
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  guard_promise m t ->
  guard_promise m[ad.X <- X] t.
Proof.
  intros * ? ? Hgp. induction t;
  try solve [try inv_vr; invc_gp; eauto with guard_promise].
  intros ? ? ? ? [? [? ?]] ?.
  repeat omicron; eauto; try discriminate;
  eapply Hgp; eauto; try eexists; eauto using acc_mem_set_X_backwards.
Qed.

Local Lemma gp_mem_set_tT : forall m t ad t' T',
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  m[ad].T = `w&T'` ->
  guard_promise m t ->
  guard_promise m[ad.tT <- t' `w&T'`] t.
Proof.
  intros * ? ? ? Hgp. induction t;
  try solve [try inv_vr; invc_gp; eauto with guard_promise].
  intros ? ? ? ? [? [? ?]] ?.
  repeat omicron; eauto; try discriminate.
  - invc H2.
    eapply Hgp; eauto.
    + eexists. admit.
    + eapply acc_mem_set_tT_backwards1; eauto.
      admit.
  - admit.
Abort.

(* preservation ------------------------------------------------------------ *)

Local Lemma gp_preservation_none : forall m t1 t2,
  guard_promise m t1 ->
  t1 --[e_none]--> t2 ->
  guard_promise m t2.
Proof.
  intros. ind_tstep; intros until 2; repeat invc_gp;
  unfold guard_promise in *; eauto using nacc_subst with not_access.
Qed.






Lemma nacc_mem_add : forall m t ad tT,
  ~ access (#m) m t ->
  (* --- *)
  ~ access ad m t ->
  ~ access ad (m +++ tT) t.
Proof.
  intros ** Hacc. induction Hacc; repeat invc_nacc; eauto; omicron; eauto.
Qed.

Local Lemma acc_mem_add : forall ad m t t' T',
  ad < #m ->
  access ad m t ->
  access ad (m +++ (t', T', false)) t.
Proof.
  intros * ? Hacc. induction Hacc; eauto using access;
  (eapply acc_memR || eapply acc_memW); eauto; omicron; eauto; invc_acc.
Qed.

Lemma acc_mem_add_backwards : forall m t ad c,
  forall_memory m (valid_references m) ->
  valid_references m t ->
  (* --- *)
  access ad (m +++ c) t ->
  access ad m t.
Proof.
  intros * ? Hvr Hacc.
  assert (Hnacc : ~ access (#m) m t) by eauto using nacc_vr_length.
  clear Hvr. induction Hacc; invc_nacc; eauto using access;
  omicron; eauto using access; invc_acc.
Qed.

Local Lemma guards_mem_add : forall adx ad m t T,
  ad < #m ->
  guards adx ad m ->
  guards adx ad (m +++ (t, T, false)).
Proof.
  intros * ? [Tx [Hadx Hacc]]. exists Tx. split;
  omicron; eauto using acc_mem_add; discriminate.
Qed.

Local Lemma guards_mem_add_backwards : forall adx ad m t T,
  forall_memory m (valid_references m) ->
  (* --- *)
  adx < #m ->
  guards adx ad (m +++ (t, T, false)) ->
  guards adx ad m.
Proof.
  intros * ? ? [Tx [Hadx Hacc]]. sigma. eexists.
  eauto using acc_mem_add_backwards.
Qed.

Local Lemma gp_preservation_alloc : forall m t1 t2 t T,
  forall_memory m (valid_references m) ->
  valid_references m t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_alloc (#m) t T]--> t2 ->
  guard_promise (m +++ (t, T, false)) t2.
Proof.
  intros. ind_tstep; invc_vr; invc_gp;
  repeat clean.
  - repeat aspecialize.
    intros adx ad Tw Had Hguards.
    eapply nacc_call; eauto.
    destruct Hguards as [Tx [Hadx Hacc]]. omicron; subst.
    + omicron; subst; try discriminate.
      * eapply acc_mem_add_backwards in Hacc; eauto.
        specialize (H1 adx ad Tw Had).
        eapply nacc_mem_add; eauto using nacc_vr_length.
        eapply H1.
        eexists; eauto.
      * eapply acc_mem_add_backwards in Hacc; eauto.
        contradict Hacc.
        eapply nacc_vr_length; eauto.
    + omicron; try discriminate.
      eapply acc_mem_add_backwards in Hacc; eauto using vr_tstep_alloc_term.
      eapply nacc_mem_add; eauto using nacc_vr_length.
      admit.
    + invc_acc.
Abort.


x& (Nat)

x& (&w (w& Nat))

m.acq (&t
---


m.set (t)


new t : x&T --[e]--> new t' : x&T

new t : ... --[e_none]--> newx ad t

new v : x&T --[e]--> &ad : x&T






Local Lemma gp_preservation_read : forall m t1 t2 ad,
  well_typed_term t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_read ad m[ad].t]--> t2 ->
  guard_promise m t2.
Proof.
  intros * [T Htypeof] **. generalize dependent T.
  ind_tstep; intros until 3; invc_gp; 
  try solve [invc_typeof; unfold guard_promise in *; eauto with not_access].
  match goal with
  |  Hgp : guard_promise m _
  ,  Hty : m[?ad].T = `w&?T`
  ,  Hg  : guards adx ?ad m
  |- _ =>
      specialize (Hgp adx ad T Hty Hg)
  end.
  repeat invc_typeof; invc_nacc; trivial. 
Qed.

Local Lemma wtt_tstep_write_type : forall t1 t2 ad t T,
  well_typed_term t1 ->
  t1 --[e_write ad t T]--> t2 ->
  exists Tw, T = `w&Tw`.
Proof.
  intros * [T ?] **. gendep T. ind_tstep; intros; repeat invc_typeof; eauto.
Qed.

Local Lemma gp_preservation_write : forall m t1 t2 ad t T,
  well_typed_term t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_write ad t T]--> t2 ->
  guard_promise m[ad.tT <- t T] t2.
Proof.
  intros. ind_tstep; invc_wtt; invc_gp.
  - eapply gp_call; eauto.
    duplicate H1 Htstep.
    eapply wtt_tstep_write_type in H1 as [? ?]; eauto; subst.
    clean.
Abort.

Local Lemma gp_preservation_acq : forall m t1 t2 ad t,
  forall_memory m (valid_references m) ->
  valid_references m t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_acq ad t]--> t2 ->
  guard_promise m[ad.X <- true] t2.
Proof.
  intros. ind_tstep; invc_vr; invc_gp;
  eauto using gp_mem_set_X with guard_promise.
Qed.

Local Lemma gp_preservation_rel : forall m t1 t2 ad,
  forall_memory m value ->
  forall_memory m (valid_references m) ->
  valid_references m t1 ->
  safe_boundaries t1 ->
  (* --- *)
  guard_promise m t1 ->
  t1 --[e_rel ad]--> t2 ->
  guard_promise m[ad.X <- false] t2.
Proof.
  intros. ind_tstep; invc_vr; invc_sb; invc_gp;
  eauto using gp_mem_set_X with guard_promise.
  eapply gp_mem_set_X; eauto. intros until 2.
  invc_sval; eauto with not_access; invc_vr; intros ?; invc_acc; eauto.
  eapply nwacc_from_safe_type; eauto.
  eapply ptyp_wacc_correlation; eauto.
Qed.

Local Lemma gp_preservation_spawn : forall m t1 t2 tid t,
  guard_promise m t1 ->
  t1 --[e_spawn tid t]--> t2 ->
  guard_promise m t2.
Proof.
  intros. ind_tstep; intros until 2; repeat invc_gp;
  unfold guard_promise in *; eauto with not_access.
Qed.

Local Lemma gp_preservation_mstep : forall m1 m2 t1 t2 e,
  forall_memory m1 value ->
  well_typed_term t1 ->
  forall_memory m1 (valid_references m1) ->
  valid_references m1 t1 ->
  safe_boundaries t1 ->
  (* --- *)
  guard_promise m1 t1 ->
  m1 / t1 ==[e]==> m2 / t2 ->
  guard_promise m2 t2.
Proof.
  intros. invc_mstep;
  eauto using gp_preservation_none;
  (* eauto using gp_preservation_alloc; *)
  eauto using gp_preservation_read;
  (* eauto using gp_preservation_write; *)
  eauto using gp_preservation_acq;
  eauto using gp_preservation_rel;
  eauto using gp_preservation_spawn.
  - admit.
  - admit.
Qed.

Theorem gp_preservation : forall m1 m2 ths1 ths2 tid e,
  forall_threads ths1 well_typed_term ->
  forall_threads ths1 (valid_references m1) ->
  (* --- *)
  forall_threads ths1 (guard_promise m1) ->
  m1 / ths1 ~~[tid, e]~~> m2 / ths2 ->
  forall_threads ths2 (guard_promise m2).
Proof.
  intros. invc_cstep.
Qed.
















































