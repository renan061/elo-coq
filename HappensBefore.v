From Coq Require Import Lia.
From Coq Require Import Lists.List.

From Elo Require Import Core.


Theorem always_happens_before : forall m m' ths ,
  m / ths ~~[tc]~~>* m' / ths' ->
  tc[evA] = (tid1, e_write ad v1 T1) ->
  tc[evB] = (tid2, e_write ad v2 T2) ->
  evA < evB ->
  evA << evB in tc.
Proof.
Abort.

Theorem always_happens_before :
  forall mA mX mY mB thsA thsX thsY thsB tid1 tid2 ad v1 v2 tc T,
    mA / thsA ~~[ tid1, e_write ad v1 T ]~~>  mX / thsX ->
    mX / thsX ~~[ tc                    ]~~>* mY / thsY ->
    mY / thsY ~~[ tid2, e_read ad v2    ]~~>  mB / thsB ->
    0 << (#tc + 1) in
      ((tid2, e_read ad v2) :: tc ++ (tid1, e_write ad v1 T) :: nil).
Proof.
  intros. destruct (nat_eq_dec tid1 tid2); subst.
  - eapply hb_thread.
    + lia.
    + clear H. clear H0. clear H1.
      simpl. induction tc.
      * eauto.
      * simpl in *.
Qed.
