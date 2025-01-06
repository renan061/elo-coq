From Elo Require Import Core.

From Elo Require Import TypeProperties.

Theorem mreg_preservation_cstep : forall m1 m2 ths1 ths2 tid e ad,
  m1 \ ths1 ~~[tid, e]~~> m2 \ ths2 ->
  ad < #m1 ->
  m1[ad].R = m2[ad].R.
Proof.
  intros. invc_cstep; trivial. invc_mstep; sigma; trivial; omicron; trivial.
Qed.

Theorem mreg_preservation_rstep : forall m1 m2 ths1 ths2 tid e ad,
  m1 \ ths1 ~~~[tid, e]~~> m2 \ ths2 ->
  ad < #m1 ->
  m1[ad].R = m2[ad].R.
Proof.
  intros. invc_rstep; eauto using mreg_preservation_cstep.
  repeat omicron; upsilon; eauto using mreg_preservation_cstep;
  invc_cstep; invc_mstep; sigma; auto.
Qed.

Theorem mreg_preservation_ustep : forall m1 m2 ths1 ths2 tc ad,
  m1 \ ths1 ~~[tc]~~>* m2 \ ths2 ->
  ad < #m1 ->
  m1[ad].R = m2[ad].R.
Proof.
  intros. ind_ustep; trivial. rewrite IHmultistep;
  eauto using ustep_nondecreasing_memory_size, mreg_preservation_rstep.
Qed.

