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

(* TODO: write_value *)
Lemma anyt_write_generalization : forall P t t' ad v T,
  anyt P v ->
  t --[EF_Write ad v T]--> t' ->
  anyt P t.
Proof.
  intros. induction_tstep; eauto using anyt.
Qed.

Lemma anyt_alloc_value_generalization : forall P t t' ad v T,
  anyt P v ->
  t --[EF_Alloc ad v T]--> t' ->
  anyt P t.
Proof.
  intros. induction_tstep; eauto using anyt.
Qed.

(* ------------------------------------------------------------------------- *)
(* anyT - anyt ignoring spawn blocks                                         *)
(* ------------------------------------------------------------------------- *)

Inductive anyT (P : tm -> Prop) : tm -> Prop :=
  | anyT_unit   :                P <{ unit }>       -> anyT P <{ unit }>
  | anyT_num    : forall n,      P <{ N n }>        -> anyT P <{ N n }>
  | anyT_ad     : forall ad T,   P <{ &ad :: T }>   -> anyT P <{ &ad :: T }>
  | anyT_new    : forall T t,    P <{ new T t }>    -> anyT P <{ new T t }>
  | anyT_new1   : forall T t,    anyT P t           -> anyT P <{ new T t }>
  | anyT_load   : forall t,      P <{ *t }>         -> anyT P <{ *t }>
  | anyT_load1  : forall t,      anyT P t           -> anyT P <{ *t }>
  | anyT_asg    : forall t1 t2,  P <{ t1 = t2 }>    -> anyT P <{ t1 = t2 }>
  | anyT_asg1   : forall t1 t2,  anyT P t1          -> anyT P <{ t1 = t2 }>
  | anyT_asg2   : forall t1 t2,  anyT P t2          -> anyT P <{ t1 = t2 }>
  | anyT_var    : forall x,      P <{ var x }>      -> anyT P <{ var x }>
  | anyT_fun    : forall x Tx t, P <{ fn x Tx t }>  -> anyT P <{ fn x Tx t }>
  | anyT_fun1   : forall x Tx t, anyT P t           -> anyT P <{ fn x Tx t }>
  | anyT_call   : forall t1 t2,  P <{ call t1 t2 }> -> anyT P <{ call t1 t2 }>
  | anyT_call1  : forall t1 t2,  anyT P t1          -> anyT P <{ call t1 t2 }>
  | anyT_call2  : forall t1 t2,  anyT P t2          -> anyT P <{ call t1 t2 }>
  | anyT_seq    : forall t1 t2,  P <{ t1; t2 }>     -> anyT P <{ t1; t2 }>
  | anyT_seq1   : forall t1 t2,  anyT P t1          -> anyT P <{ t1; t2 }>
  | anyT_seq2   : forall t1 t2,  anyT P t2          -> anyT P <{ t1; t2 }>
  | anyT_spawn  : forall t,      P <{ spawn t }>    -> anyT P <{ spawn t }>
  .

(* Alternative access for the future

Inductive has_access : mem -> addr -> tm -> Prop :=
  | has_access_mem : forall m ad ad' T,
    ad <> ad' ->
    anyT (has_access m ad) m[ad'].tm ->
    has_access m ad <{ &ad' :: T}> 

  | has_access_ad : forall m ad T,
    has_access m ad <{ &ad :: T}>
  .

Definition access m t ad := anyT (has_access m ad) t.
*)
