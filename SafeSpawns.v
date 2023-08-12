From Elo Require Import Util.
From Elo Require Import Core.
From Elo Require Import CoreExt.

(* ------------------------------------------------------------------------- *)
(* no-mut                                                                    *)
(* ------------------------------------------------------------------------- *)

(* A term is no-mut if it has no mutable references. *)
Inductive no_mut : tm -> Prop :=
  | nomut_unit :
    no_mut <{unit}>

  | nomut_num : forall n,
    no_mut <{N n}>

  | nomut_ad : forall ad T,
    no_mut <{&ad :: i&T}>

  | nomut_new : forall T t,
    no_mut t ->
    no_mut <{new T t}>

  | nomut_load : forall t,
    no_mut t ->
    no_mut <{*t}>

  | nomut_asg : forall t1 t2,
    no_mut t1 ->
    no_mut t2 ->
    no_mut <{t1 = t2}>

  | nomut_var : forall x,
    no_mut <{var x}>

  | nomut_fun : forall x Tx t,
    no_mut t ->
    no_mut <{fn x Tx t}>

  | nomut_call : forall t1 t2,
    no_mut t1 ->
    no_mut t2 ->
    no_mut <{call t1 t2}>

  | nomut_seq : forall t1 t2,
    no_mut t1 ->
    no_mut t2 ->
    no_mut <{t1; t2}>

  | nomut_spawn : forall t,
    no_mut t ->
    no_mut <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-spawns                                                               *)
(* ------------------------------------------------------------------------- *)

(* A term has safe spawns if all of its spawns have no mutable references. *)
Inductive safe_spawns : tm -> Prop :=
  | ss_unit :
      safe_spawns <{unit}>

  | ss_num : forall n,
      safe_spawns <{N n}>

  | ss_ad : forall ad T,
      safe_spawns <{&ad :: T}>

  | ss_new : forall T t,
      safe_spawns t ->
      safe_spawns <{new T t}>

  | ss_load : forall t,
      safe_spawns t ->
      safe_spawns <{*t}>

  | ss_asg : forall t1 t2,
      safe_spawns t1 ->
      safe_spawns t2 ->
      safe_spawns <{t1 = t2}>

  | ss_var : forall x,
      safe_spawns <{var x}>

  | ss_fun : forall x Tx t,
      safe_spawns t ->
      safe_spawns <{fn x Tx t}>

  | ss_call : forall t1 t2,
      safe_spawns t1 ->
      safe_spawns t2 ->
      safe_spawns <{call t1 t2}>

  | ss_seq : forall t1 t2,
      safe_spawns t1 ->
      safe_spawns t2 ->
      safe_spawns <{t1; t2}>

  | ss_spawn : forall t,
      no_mut t ->
      safe_spawns <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* has-var                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive has_var (x : id) : tm  -> Prop :=
  | hv_new : forall T t,
    has_var x t ->
    has_var x <{new T t}>

  | hv_load : forall t,
    has_var x t ->
    has_var x <{*t}>

  | hv_asg1 : forall t1 t2,
    has_var x t1 ->
    has_var x <{t1 = t2}>

  | hv_asg2 : forall t1 t2,
    has_var x t2 ->
    has_var x <{t1 = t2}>

  | hv_var :
    has_var x <{var x}>

  | hv_fun : forall x' Tx t,
    x <> x' ->
    has_var x t ->
    has_var x <{fn x' Tx t}>

  | hv_call1 : forall t1 t2,
    has_var x t1 ->
    has_var x <{call t1 t2}>

  | hv_call2 : forall t1 t2,
    has_var x t2 ->
    has_var x <{call t1 t2}>

  | hv_seq1 : forall t1 t2,
    has_var x t1 ->
    has_var x <{t1; t2}>

  | hv_seq2 : forall t1 t2,
    has_var x t2 ->
    has_var x <{t1; t2}>

  | hv_spawn : forall t,
    has_var x t ->
    has_var x <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* no-mut inversion                                                          *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_nomut tactic :=
  match goal with
  (* irrelevant for unit      *)
  (* irrelevant for num       *)
  | H : no_mut <{& _ :: Unit     }> |- _ => tactic H
  | H : no_mut <{& _ :: Num      }> |- _ => tactic H
  (* irrelevant if &ad :: i&T *)
  | H : no_mut <{& _ :: & _      }> |- _ => tactic H
  | H : no_mut <{& _ :: (_ --> _)}> |- _ => tactic H
  | H : no_mut <{new _ _         }> |- _ => tactic H
  | H : no_mut <{* _             }> |- _ => tactic H
  | H : no_mut <{_ = _           }> |- _ => tactic H
  (* irrelevant for var       *)
  | H : no_mut <{fn _ _ _        }> |- _ => tactic H
  | H : no_mut <{call _ _        }> |- _ => tactic H
  | H : no_mut <{_ ; _           }> |- _ => tactic H
  | H : no_mut <{spawn _         }> |- _ => tactic H
  end.

Ltac inv_nomut := match_nomut inv.

Ltac invc_nomut := match_nomut invc.

(* ------------------------------------------------------------------------- *)
(* safe-spawns inversion                                                     *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_ss tactic :=
  match goal with
  (* irrelevant for unit *)
  (* irrelevant for num  *)
  (* irrelevant for ad   *)
  | H : safe_spawns <{new _ _ }> |- _ => tactic H
  | H : safe_spawns <{* _     }> |- _ => tactic H
  | H : safe_spawns <{_ = _   }> |- _ => tactic H
  (* irrelevant for var  *)
  | H : safe_spawns <{fn _ _ _}> |- _ => tactic H
  | H : safe_spawns <{call _ _}> |- _ => tactic H
  | H : safe_spawns <{_ ; _   }> |- _ => tactic H
  | H : safe_spawns <{spawn _ }> |- _ => tactic H
  end.

Ltac inv_ss := match_ss inv.

Ltac invc_ss := match_ss invc.

(* ------------------------------------------------------------------------- *)
(* has-var inversion                                                         *)
(* ------------------------------------------------------------------------- *)

Local Ltac match_hasvar tactic :=
  match goal with
  | H : has_var _  thread_default |- _ => tactic H
  | H : has_var _  <{unit    }>   |- _ => tactic H
  | H : has_var _  <{N _     }>   |- _ => tactic H
  | H : has_var _  <{& _ :: _}>   |- _ => tactic H
  | H : has_var _  <{new _ _ }>   |- _ => tactic H
  | H : has_var _  <{* _     }>   |- _ => tactic H
  | H : has_var _  <{_ = _   }>   |- _ => tactic H
  | H : has_var ?x <{var ?x  }>   |- _ => fail
  | H : has_var ?x <{var ?y  }>   |- _ => tactic H
  | H : has_var _  <{fn _ _ _}>   |- _ => tactic H
  | H : has_var _  <{call _ _}>   |- _ => tactic H
  | H : has_var _  <{_ ; _   }>   |- _ => tactic H
  | H : has_var _  <{spawn _ }>   |- _ => tactic H
  end.

Ltac inv_hasvar := match_hasvar inv.

Ltac invc_hasvar := match_hasvar invc.

(* ------------------------------------------------------------------------- *)
(* independent properties                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma nomut_then_ss : forall t,
  no_mut t ->
  safe_spawns t.
Proof.
  intros * H. induction t; induction H; eauto using safe_spawns.
Qed.

Lemma hasvar_dec : forall x t,
  Decidable.decidable (has_var x t).
Proof.
  unfold Decidable.decidable. intros. induction t;
  try progress (repeat match goal with H : _ \/ _ |- _ => destruct H end);
  try match goal with x' : id |- _ => destruct (string_eq_dec x x'); subst end;
  solve [ left; eauto using has_var
        | right; intros ?; inv_hasvar; eauto
        ].
Qed.

Lemma ss_tstep_alloc_value : forall t t' ad v T,
  safe_spawns t ->
  t --[EF_Alloc ad v T]--> t' ->
  safe_spawns v.
Proof.
  intros. induction_tstep; inv_ss; eauto.
Qed.

Lemma ss_tstep_write_value : forall t t' ad v T,
  safe_spawns t ->
  t --[EF_Write ad v T]--> t' ->
  safe_spawns v.
Proof.
  intros. induction_tstep; inv_ss; eauto.
Qed.

