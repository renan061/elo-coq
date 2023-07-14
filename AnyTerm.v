From Elo Require Import Util.
From Elo Require Import Core.
From Elo Require Import CoreExt.

(* ------------------------------------------------------------------------- *)
(* anyt                                                                      *)
(* ------------------------------------------------------------------------- *)

Inductive anyt (P : tm -> Prop) : tm -> Prop :=
  | anyt_unit   :                P <{ unit }>       -> anyt P <{ unit }>
  | anyt_num    : forall n,      P <{ N n }>        -> anyt P <{ N n }>
  | anyt_ad     : forall ad T,   P <{ &ad :: T }>   -> anyt P <{ &ad :: T }>
  | anyt_new    : forall T t,    P <{ new T t }>    -> anyt P <{ new T t }>
  | anyt_new1   : forall T t,    anyt P t           -> anyt P <{ new T t }>
  | anyt_load   : forall t,      P <{ *t }>         -> anyt P <{ *t }>
  | anyt_load1  : forall t,      anyt P t           -> anyt P <{ *t }>
  | anyt_asg    : forall t1 t2,  P <{ t1 = t2 }>    -> anyt P <{ t1 = t2 }>
  | anyt_asg1   : forall t1 t2,  anyt P t1          -> anyt P <{ t1 = t2 }>
  | anyt_asg2   : forall t1 t2,  anyt P t2          -> anyt P <{ t1 = t2 }>
  | anyt_var    : forall x,      P <{ var x }>      -> anyt P <{ var x }>
  | anyt_fun    : forall x Tx t, P <{ fn x Tx t }>  -> anyt P <{ fn x Tx t }>
  | anyt_fun1   : forall x Tx t, anyt P t           -> anyt P <{ fn x Tx t }>
  | anyt_call   : forall t1 t2,  P <{ call t1 t2 }> -> anyt P <{ call t1 t2 }>
  | anyt_call1  : forall t1 t2,  anyt P t1          -> anyt P <{ call t1 t2 }>
  | anyt_call2  : forall t1 t2,  anyt P t2          -> anyt P <{ call t1 t2 }>
  | anyt_seq    : forall t1 t2,  P <{ t1; t2 }>     -> anyt P <{ t1; t2 }>
  | anyt_seq1   : forall t1 t2,  anyt P t1          -> anyt P <{ t1; t2 }>
  | anyt_seq2   : forall t1 t2,  anyt P t2          -> anyt P <{ t1; t2 }>
  | anyt_spawn  : forall t,      P <{ spawn t }>    -> anyt P <{ spawn t }>
  | anyt_spawn1 : forall t,      anyt P t           -> anyt P <{ spawn t }>
  .

(* Since <v> is inside <t>: *)

Lemma anyt_write_generalization : forall P t t' ad v V,
  anyt P v ->
  t --[EF_Write ad v V]--> t' ->
  anyt P t.
Proof.
  intros. induction_step; eauto using anyt.
Qed.

Lemma anyt_alloc_generalization : forall P t t' ad v V,
  anyt P v ->
  t --[EF_Alloc ad v V]--> t' ->
  anyt P t.
Proof.
  intros. induction_step; eauto using anyt.
Qed.

