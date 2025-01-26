From Coq Require Import Lists.List.

From Elo Require Import Core.

Notation "'<<' ev1 ',' tc ',' ev2 '>>'" := (ev2 :: tc +++ ev1).

(* ------------------------------------------------------------------------- *)
(* is-acquire & is-release                                                   *)
(* ------------------------------------------------------------------------- *)

Definition is_acquire (ad : addr) (e : eff) :=
  (exists t, e = e_acq ad t) \/ e = e_wacq ad.

Definition is_release (ad : addr) (e : eff) :=
  e = e_rel ad \/ e = e_wrel ad.

Lemma isacquire_dec : forall ad e,
  Decidable.decidable (is_acquire ad e).
Proof.
  unfold Decidable.decidable. unfold not. unfold is_acquire. intros.
  rename ad into ad'. destruct e;
  try solve [right; intros [[? F] | F]; invc F];
  nat_eq_dec ad' ad;
  try solve [right; intros [[? F] | F]; invc F; congruence];
  eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* happens-before                                                            *)
(* ------------------------------------------------------------------------- *)

Inductive happens_before : trace -> Prop :=
  | hb_thread : forall tc tid e1 e2,
    happens_before ((tid, e2) :: tc +++ (tid, e1))

  | hb_release_acquire : forall tc tid1 tid2 ad e1 e2,
    is_release ad e1 ->
    is_acquire ad e2 ->
    happens_before ((tid2, e2) :: tc +++ (tid1, e1))

  | hb_initialize_acquire : forall tc tid1 tid2 ad t e,
    is_acquire ad e ->
    happens_before ((tid2, e) :: tc +++ (tid1, e_init ad t))

  | hb_transitivity : forall tcA tcB ev1 ev2 ev3,
    happens_before (ev2 :: tcA +++ ev1) ->
    happens_before (ev3 :: tcB +++ ev2) ->
    happens_before (ev3 :: tcB ++ ev2 :: tcA +++ ev1)
  .

(* lemmas ------------------------------------------------------------------ *)

Lemma happens_before_from_initialize_acquire_effects :
  forall tc tc1 tc2 tc3 tid1 tid2 e1 e2 eAcq eInit ad t,
    is_acquire ad eAcq  ->
    eInit = e_init ad t ->
    tc = (tc3 ++ (tid2, eAcq) :: tc2 ++ (tid1, eInit) :: tc1) ->
    happens_before <<(tid1, e1), tc, (tid2, e2)>>.
Proof.
  intros * ? ? Htc.
  rewrite app_comm_cons in Htc. rewrite app_assoc in Htc.
  remember (tc3 ++ (tid2, eAcq) :: tc2) as tc' eqn: Htc'.
  rewrite Htc. clear Htc.
  unfold add. rewrite <- app_assoc. rewrite <- app_comm_cons.
  eapply hb_transitivity; eauto using happens_before.
  rewrite Htc'. clear Htc'.
  unfold add. rewrite <- app_assoc. rewrite <- app_comm_cons.
  subst.
  eapply hb_transitivity; eauto using happens_before.
Qed.

