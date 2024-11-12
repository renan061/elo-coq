From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Sem.
From Elo Require Import SemExt.

(* ------------------------------------------------------------------------- *)
(* forall-threads                                                            *)
(* ------------------------------------------------------------------------- *)

Local Lemma forall_threads_step {P : tm -> Prop} : forall ths tid t,
  P <{unit}> ->
  P t ->
  forall_threads ths P ->
  forall_threads ths[tid <- t] P.
Proof.
  intros ** ?. repeat omicron; auto.
Qed.

Local Lemma forall_threads_spawn {P : tm -> Prop} : forall ths tid t1 t2,
  P <{unit}> ->
  (P t1 /\ P t2) -> 
  forall_threads ths P ->
  forall_threads (ths[tid <- t1] +++ t2) P.
Proof.
  intros * ? [? ?] ? ?. repeat omicron; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* forall-threads (P m)                                                      *)
(* ------------------------------------------------------------------------- *)

Local Lemma forall_threads_add_step {P : mem -> tm -> Prop} :
  forall m c ths tid t,
    (P (m +++ c) <{unit}> /\
     P (m +++ c) t        /\
     (forall tid', tid <> tid' -> P (m +++ c) ths[tid'])) ->
    forall_threads ths (P m) ->
    forall_threads ths[tid <- t] (P (m +++ c)).
Proof.
  intros * [? [? ?]] ** ?. repeat omicron; eauto.
Qed.

Local Lemma forall_threads_sett_step {P : mem -> tm -> Prop} :
  forall m ths tid ad t1 t2,
    (P m[ad.t <- t2] <{unit}> /\
     P m[ad.t <- t2] t1       /\
     (forall tid', tid <> tid' -> P m[ad.t <- t2] ths[tid'])) ->
    forall_threads ths (P m) ->
    forall_threads ths[tid <- t1] (P m[ad.t <- t2]).
Proof.
  intros * [? [? ?]] ** ?. repeat omicron; eauto.
Qed.

Local Lemma forall_threads_setx_step {P : mem -> tm -> Prop} :
  forall m ths tid ad t X,
    (P m[ad.X <- X] <{unit}> /\
     P m[ad.X <- X] t        /\
     (forall tid', tid <> tid' -> P m[ad.X <- X] ths[tid'])) ->
    forall_threads ths (P m) ->
    forall_threads ths[tid <- t] (P m[ad.X <- X]).
Proof.
  intros * [? [? ?]] ** ?. repeat omicron; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* forall-program                                                            *)
(* ------------------------------------------------------------------------- *)

Local Lemma fp_step {P : tm -> Prop} : forall m ths tid t,
  P <{unit}> ->
  P t ->
  forall_program m ths P ->
  forall_program m ths[tid <- t] P.
Proof.
  intros * ? ? [? ?]. split; trivial.
  intros ?. repeat omicron; eauto.
Qed.

Local Lemma fp_add_step {P : tm -> Prop} : forall m ths tid t T,
  P <{unit}> ->
  P t ->
  forall_program m ths P ->
  forall_program (m +++ (None, T, false)) ths[tid <- t] P.
Proof.
  intros * ? ? [? ?]. split.
  - intros until 1. omicron; simpl in *; eauto.
  - intros ?. repeat omicron; trivial.
Qed.

Local Lemma fp_sett_step {P : tm -> Prop} :
  forall m ths ad t1 tid t2,
    P <{unit}> ->
    (P t1 /\ P t2) -> 
    forall_program m ths P ->
    forall_program m[ad.t <- t1] ths[tid <- t2] P.
Proof.
  intros * ? [? ?] [? ?]. split.
  - intros until 1. repeat omicron; simpl in *; eauto. invc_eq; eauto.
  - intros ?. repeat omicron; trivial.
Qed.

Local Lemma fp_setx_step {P : tm -> Prop} : forall m ths ad X tid t,
  P <{unit}> ->
  P t ->
  forall_program m ths P ->
  forall_program m[ad.X <- X] ths[tid <- t] P.
Proof.
  intros * ? ? [? ?]. split.
  - intros until 1. repeat omicron; simpl in *; eauto.
  - intros ?. repeat omicron; trivial.
Qed.

Local Lemma fp_spawn {P : tm -> Prop} : forall m ths tid t1 t2,
  P <{unit}> ->
  (P t1 /\ P t2) -> 
  forall_program m ths P ->
  forall_program m (ths[tid <- t1] +++ t2) P.
Proof.
  intros * ? [? ?] [? ?]. split.
  - intros until 1. repeat omicron; eauto.
  - intros ?. repeat omicron; trivial.
Qed.

(* ------------------------------------------------------------------------- *)
(* memory                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma setx_get_tm_eq : forall m ad ad' X,
  m[ad.X <- X][ad'].t = m[ad'].t.
Proof.
  intros. repeat omicron; trivial.
Qed.

Lemma setx_get_ty_eq : forall m ad ad' X,
  m[ad.X <- X][ad'].T = m[ad'].T.
Proof.
  intros. repeat omicron; trivial.
Qed.

Lemma add_getx_false : forall m ad T,
  (m +++ (None, T, false))[ad].X = false <-> m[ad].X = false.
Proof.
  intros; split; omicron; trivial.
Qed.

Lemma add_getx_true : forall m ad T,
  (m +++ (None, T, false))[ad].X = true <-> (ad < #m /\ m[ad].X = true).
Proof.
  intros. split.
  - omicron; simpl in *; auto.
  - intros [? ?]. sigma. assumption.
Qed.

(* ------------------------------------------------------------------------- *)

Local Lemma add_gett_none : forall m ad T,
  (m +++ (None, T, false))[ad].t = None <-> m[ad].t = None.
Proof.
  intros; split; omicron; trivial.
Qed.

Local Lemma add_gett_some : forall m t ad T,
  (m +++ (None, T, false))[ad].t = Some t <-> (ad < #m /\ m[ad].t = Some t).
Proof.
  intros. split.
  - omicron; simpl in *; auto.
  - intros [? ?]. sigma. assumption.
Qed.

Local Lemma add_get_nonone : forall m ad T,
  (m +++ (None, T, false))[ad].t <> None ->
  (m[ad].t <> None /\ ad < #m).
Proof.
  intros. omicron; simpl in *; auto.
Qed.

Local Lemma add_get_some : forall m t ad T,
  (m +++ (None, T, false))[ad].t = Some t <-> m[ad].t = Some t.
Proof.
  intros. split; omicron; trivial.
Qed.

Local Lemma set_get_none1 : forall m ad ad' t,
  ad' < #m ->
  m[ad'.t <- t][ad].t = None ->
  (m[ad].t = None /\ ad <> ad').
Proof.
  intros. omicron; simpl in *; auto.
Qed.

Local Lemma set_get_none2 : forall m ad ad' t,
  ad < #m ->
  m[ad'.t <- t][ad].t = None ->
  (m[ad].t = None /\ ad <> ad').
Proof.
  intros. omicron; simpl in *; auto.
Qed.

Local Lemma set_get_some : forall m ad ad' t t',
  m[ad'.t <- t'][ad].t = Some t ->
  (ad = ad' /\ t = t') \/ (ad <> ad' /\ m[ad].t = Some t).
Proof.
  intros. repeat omicron; simpl in *; auto. invc_eq. auto.
Qed.
   
(* ------------------------------------------------------------------------- *)

Ltac upsilon' :=
  match goal with
  (* ---------------------------------------- *)
  (* misc                                     *)
  (* ---------------------------------------- *)
  | H : Some ?x = Some ?y |- _ => invc H
  (* ---------------------------------------- *)
  (* cell                                     *)
  (* ---------------------------------------- *)
  | H : context C [ (_, _, _).t ] |- _ => simpl in H
  | |-  context C [ (_, _, _).t ]      => simpl
  (* ---------------------------------------- *)
  | H : context C [ (_, _, _).T ] |- _ => simpl in H
  | |-  context C [ (_, _, _).T ]      => simpl
  (* ---------------------------------------- *)
  | H : context C [ (_, _, _).X ] |- _ => simpl in H
  | |-  context C [ (_, _, _).X ]      => simpl
  (* ---------------------------------------- *)
  (* forall-threads                           *)
  (* ---------------------------------------- *)
  | H : forall_threads ?ths ?P
  |-    forall_threads ?ths[_ <- _] ?P =>
    eapply forall_threads_step; trivial; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_threads ?ths ?P
  |-    forall_threads (?ths[_ <- _] +++ _) ?P =>
    eapply forall_threads_spawn; trivial; try solve [constructor]; split
  (* ---------------------------------------- *)
  (* forall-threads (P m)                     *)
  (* ---------------------------------------- *)
  | H : forall_threads ?ths (?P ?m)
  |-    forall_threads ?ths[_ <- _] (?P (?m +++ _)) =>
    eapply forall_threads_add_step; trivial;
    split; try split; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_threads ?ths (?P ?m)
  |-    forall_threads ?ths[_ <- _] (?P ?m[_.t <- _]) =>
    eapply forall_threads_sett_step; trivial;
    split; try split; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_threads ?ths (?P ?m)
  |-    forall_threads ?ths[_ <- _] (?P ?m[_.X <- _]) =>
    eapply forall_threads_setx_step; trivial;
    split; try split; try solve [constructor]
  (* ---------------------------------------- *)
  (* forall-program                           *)
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program ?m ?ths[_ <- _] ?P =>
    eapply fp_step; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program (?m +++ (None, _, false)) ?ths[_ <- _] ?P =>
    eapply fp_add_step; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program ?m[_.t <- _] ?ths[_ <- _] ?P =>
    eapply fp_sett_step; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program ?m[_.X <- _] ?ths[_ <- _] ?P =>
    eapply fp_setx_step; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  | H : forall_program ?m ?ths ?P
  |-    forall_program ?m (?ths[_ <- _] +++ _) ?P =>
      eapply fp_spawn; eauto; try solve [constructor]
  (* ---------------------------------------- *)
  (* memory -- X                              *)
  (* ---------------------------------------- *)
  | H : context C [ ?m[?ad'.X <- ?X][?ad].t ] |- _ =>
    rewrite setx_get_tm_eq in H
  |  |- context C [ ?m[?ad'.X <- ?X][?ad].t ] =>
    rewrite setx_get_tm_eq 
  (* ---------------------------------------- *)
  | H : context C [ ?m[?ad'.X <- ?X][?ad].T ] |- _ =>
    rewrite setx_get_ty_eq in H
  |  |- context C [ ?m[?ad'.X <- ?X][?ad].T ] =>
    rewrite setx_get_ty_eq 
  (* ---------------------------------------- *)
  | H : (_ +++ (None, _, false))[_].X = false |- _ =>
    rewrite add_getx_false in H
  (* ---------------------------------------- *)
  | H : (_ +++ (None, _, false))[_].X = true  |- _ =>
    eapply add_getx_true in H as [? ?]
  (* ---------------------------------------- *)
  (* memory -- t                              *)
  (* ---------------------------------------- *)
  | H : (_ +++ (None, _, false))[_].t = None |- _ =>
    rewrite add_gett_none in H
  (* ---------------------------------------- *)
  | H : (_ +++ (None, _, false))[_].t = Some _ |- _ =>
    eapply add_gett_some in H as [? ?]
  (* ---------------------------------------- *)
  | H : (_ +++ (None, _, false))[_].t <> None |- _ =>
    eapply add_get_nonone in H as [?Ha ?Hb]; clear H
  (* ---------------------------------------- *)
  | Had' : ?ad' < #?m, H : ?m[?ad'.t <- ?t][?ad].t = None |- _ =>
    apply (set_get_none1 m ad ad' t Had') in H as [? ?]
  (* ---------------------------------------- *)
  | Had  : ?ad  < #?m, H : ?m[?ad'.t <- ?t][?ad].t = None |- _ =>
    apply (set_get_none2 m ad ad' t Had)  in H as [? ?]
  (* ---------------------------------------- *)
  | H : ?m[?ad'.t <- ?t'][?ad].t = Some ?t |- _ =>
    apply (set_get_some m ad ad' t t') in H as [[? ?] | [? ?]]; subst
  end.

Ltac upsilon := repeat upsilon'.

