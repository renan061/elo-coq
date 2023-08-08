From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-mut                                                                    *)
(* ------------------------------------------------------------------------- *)

(* A term is no-mut if it has no mutable references. *)
Inductive NoMut : tm -> Prop :=
  | nomut_unit :
    NoMut <{unit}>

  | nomut_num : forall n,
    NoMut <{N n}>

  | nomut_refI : forall ad T,
    NoMut <{&ad :: i&T}>

  | nomut_new : forall T t,
    NoMut t ->
    NoMut <{new T t}>

  | nomut_load : forall t,
    NoMut t ->
    NoMut <{*t}>

  | nomut_asg : forall t1 t2,
    NoMut t1 ->
    NoMut t2 ->
    NoMut <{t1 = t2}>

  | nomut_var : forall x,
    NoMut <{var x}>

  | nomut_fun : forall x Tx t,
    NoMut t ->
    NoMut <{fn x Tx t}>

  | nomut_call : forall t1 t2,
    NoMut t1 ->
    NoMut t2 ->
    NoMut <{call t1 t2}>

  | nomut_seq : forall t1 t2,
    NoMut t1 ->
    NoMut t2 ->
    NoMut <{t1; t2}>

  | nomut_spawn : forall t,
    NoMut t ->
    NoMut <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* safe-spawns                                                               *)
(* ------------------------------------------------------------------------- *)

(* A term has safe spawns if all of its spawns have no mutable references. *)
Inductive SafeSpawns : tm -> Prop :=
  | ss_unit :
      SafeSpawns <{unit}>

  | ss_num : forall n,
      SafeSpawns <{N n}>

  | ss_ref : forall ad T,
      SafeSpawns <{&ad :: T}>

  | ss_new : forall T t,
      SafeSpawns t ->
      SafeSpawns <{new T t}>

  | ss_load : forall t,
      SafeSpawns t ->
      SafeSpawns <{*t}>

  | ss_asg : forall t1 t2,
      SafeSpawns t1 ->
      SafeSpawns t2 ->
      SafeSpawns <{t1 = t2}>

  | ss_var : forall x,
      SafeSpawns <{var x}>

  | ss_fun : forall x Tx t,
      SafeSpawns t ->
      SafeSpawns <{fn x Tx t}>

  | ss_call : forall t1 t2,
      SafeSpawns t1 ->
      SafeSpawns t2 ->
      SafeSpawns <{call t1 t2}>

  | ss_seq : forall t1 t2,
      SafeSpawns t1 ->
      SafeSpawns t2 ->
      SafeSpawns <{t1; t2}>

  | ss_spawn : forall t,
      NoMut t ->
      SafeSpawns <{spawn t}>
  .

(* ------------------------------------------------------------------------- *)
(* has-var                                                                   *)
(* ------------------------------------------------------------------------- *)

Inductive HasVar (x : id) : tm  -> Prop :=
  | hasvar_new : forall T t,
      HasVar x t ->
      HasVar x <{new T t}>

  | hasvar_load : forall t,
      HasVar x t ->
      HasVar x <{*t}>

  | hasvar_asg1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{t1 = t2}>

  | hasvar_asg2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{t1 = t2}>

  | hasvar_var :
      HasVar x <{var x}>

  | hasvar_fun : forall x' Tx t,
      x <> x' ->
      HasVar x t ->
      HasVar x <{fn x' Tx t}>

  | hasvar_call1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{call t1 t2}>

  | hasvar_call2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{call t1 t2}>

  | hasvar_seq1 : forall t1 t2,
      HasVar x t1 ->
      HasVar x <{t1; t2}>

  | hasvar_seq2 : forall t1 t2,
      HasVar x t2 ->
      HasVar x <{t1; t2}>

  | hasvar_spawn : forall t,
      HasVar x t ->
      HasVar x <{spawn t}>
  .






















Ltac inversion_nomut :=
  match goal with
  | H : NoMut <{unit    }> |- _ => inversion H; subst
  | H : NoMut <{N _     }> |- _ => inversion H; subst
  | H : NoMut <{& _ :: _}> |- _ => inversion H; subst
  | H : NoMut <{new _ _ }> |- _ => inversion H; subst
  | H : NoMut <{* _     }> |- _ => inversion H; subst
  | H : NoMut <{_ = _   }> |- _ => inversion H; subst
  | H : NoMut <{var _   }> |- _ => inversion H; subst
  | H : NoMut <{fn _ _ _}> |- _ => inversion H; subst
  | H : NoMut <{call _ _}> |- _ => inversion H; subst
  | H : NoMut <{_ ; _   }> |- _ => inversion H; subst
  | H : NoMut <{spawn _ }> |- _ => inversion H; subst
  end.

Ltac inversion_clear_nomut :=
  match goal with
  | H : NoMut <{unit    }> |- _ => inv_clear H
  | H : NoMut <{N _     }> |- _ => inv_clear H
  | H : NoMut <{& _ :: _}> |- _ => inv_clear H
  | H : NoMut <{new _ _ }> |- _ => inv_clear H
  | H : NoMut <{* _     }> |- _ => inv_clear H
  | H : NoMut <{_ = _   }> |- _ => inv_clear H
  | H : NoMut <{var _   }> |- _ => inv_clear H
  | H : NoMut <{fn _ _ _}> |- _ => inv_clear H
  | H : NoMut <{call _ _}> |- _ => inv_clear H
  | H : NoMut <{_ ; _   }> |- _ => inv_clear H
  | H : NoMut <{spawn _ }> |- _ => inv_clear H
  end.

Local Lemma nomut_subst : forall x t t',
  NoMut t ->
  NoMut t' ->
  NoMut ([x := t'] t).
Proof.
  intros. induction t; intros;
  inversion_nomut; eauto using NoMut;
  simpl; destruct String.string_dec; subst; eauto using NoMut. 
Qed.


Ltac inversion_ss :=
  match goal with
  | H : SafeSpawns <{unit    }> |- _ => inversion H; subst
  | H : SafeSpawns <{N _     }> |- _ => inversion H; subst
  | H : SafeSpawns <{& _ :: _}> |- _ => inversion H; subst
  | H : SafeSpawns <{new _ _ }> |- _ => inversion H; subst
  | H : SafeSpawns <{* _     }> |- _ => inversion H; subst
  | H : SafeSpawns <{_ = _   }> |- _ => inversion H; subst
  | H : SafeSpawns <{var _   }> |- _ => inversion H; subst
  | H : SafeSpawns <{fn _ _ _}> |- _ => inversion H; subst
  | H : SafeSpawns <{call _ _}> |- _ => inversion H; subst
  | H : SafeSpawns <{_ ; _   }> |- _ => inversion H; subst
  | H : SafeSpawns <{spawn _ }> |- _ => inversion H; subst
  end.

Ltac inversion_clear_ss :=
  match goal with
  | H : SafeSpawns <{unit    }> |- _ => inv_clear H
  | H : SafeSpawns <{N _     }> |- _ => inv_clear H
  | H : SafeSpawns <{& _ :: _}> |- _ => inv_clear H
  | H : SafeSpawns <{new _ _ }> |- _ => inv_clear H
  | H : SafeSpawns <{* _     }> |- _ => inv_clear H
  | H : SafeSpawns <{_ = _   }> |- _ => inv_clear H
  | H : SafeSpawns <{var _   }> |- _ => inv_clear H
  | H : SafeSpawns <{fn _ _ _}> |- _ => inv_clear H
  | H : SafeSpawns <{call _ _}> |- _ => inv_clear H
  | H : SafeSpawns <{_ ; _   }> |- _ => inv_clear H
  | H : SafeSpawns <{spawn _ }> |- _ => inv_clear H
  end.

Ltac inversion_hv :=
  match goal with
  | H : HasVar _ <{unit    }> |- _ => inversion H; subst
  | H : HasVar _ <{N _     }> |- _ => inversion H; subst
  | H : HasVar _ <{& _ :: _}> |- _ => inversion H; subst
  | H : HasVar _ <{new _ _ }> |- _ => inversion H; subst
  | H : HasVar _ <{* _     }> |- _ => inversion H; subst
  | H : HasVar _ <{_ = _   }> |- _ => inversion H; subst
  | H : HasVar _ <{var _   }> |- _ => inversion H; subst
  | H : HasVar _ <{fn _ _ _}> |- _ => inversion H; subst
  | H : HasVar _ <{call _ _}> |- _ => inversion H; subst
  | H : HasVar _ <{_ ; _   }> |- _ => inversion H; subst
  | H : HasVar _ <{spawn _ }> |- _ => inversion H; subst
  end.

Ltac inversion_clear_hv :=
  match goal with
  | H : HasVar _ <{unit    }> |- _ => inv_clear H
  | H : HasVar _ <{N _     }> |- _ => inv_clear H
  | H : HasVar _ <{& _ :: _}> |- _ => inv_clear H
  | H : HasVar _ <{new _ _ }> |- _ => inv_clear H
  | H : HasVar _ <{* _     }> |- _ => inv_clear H
  | H : HasVar _ <{_ = _   }> |- _ => inv_clear H
  | H : HasVar _ <{var _   }> |- _ => inv_clear H
  | H : HasVar _ <{fn _ _ _}> |- _ => inv_clear H
  | H : HasVar _ <{call _ _}> |- _ => inv_clear H
  | H : HasVar _ <{_ ; _   }> |- _ => inv_clear H
  | H : HasVar _ <{spawn _ }> |- _ => inv_clear H
  end.

Lemma hasvar_dec : forall x t,
  Decidable.decidable (HasVar x t).
Proof.
  unfold Decidable.decidable. intros. induction t;
  try (destruct IHt); try (destruct IHt1); try (destruct IHt2);
  try match goal with
    | x : id, x' : id |- _ =>
      destruct (String.string_dec x x'); subst
  end;
  solve
    [ left; eauto using HasVar
    | right; intros F; inv_clear F; eauto; contradiction
    ].
Qed.

Local Ltac solve_not_hasvar :=
  intros; match goal with
  | |- (~ HasVar _ ?t) => induction t; eauto using HasVar
  end.

Lemma not_hv_new : forall x t T,
  ~ HasVar x <{new T t}> -> ~ HasVar x t.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_load : forall x t,
  ~ HasVar x <{*t}> -> ~ HasVar x t.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_asg1 : forall x t1 t2,
  ~ HasVar x <{t1 = t2}> -> ~ HasVar x t1.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_asg2 : forall x t1 t2,
  ~ HasVar x <{t1 = t2}> -> ~ HasVar x t2.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_fun : forall x x' t Tx,
  x <> x' -> ~ HasVar x <{fn x' Tx t}> -> ~ HasVar x t.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_call1 : forall x t1 t2,
  ~ HasVar x <{call t1 t2}> -> ~ HasVar x t1.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_call2 : forall x t1 t2,
  ~ HasVar x <{call t1 t2}> -> ~ HasVar x t2.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_seq1 : forall x t1 t2,
  ~ HasVar x <{t1; t2}> -> ~ HasVar x t1.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_seq2 : forall x t1 t2,
  ~ HasVar x <{t1; t2}> -> ~ HasVar x t2.
Proof. solve_not_hasvar. Qed.

Lemma not_hv_spawn : forall x t,
  ~ HasVar x <{spawn t}> -> ~ HasVar x t.
Proof. solve_not_hasvar. Qed.

Lemma hasvar_subst : forall x t tx,
  ~ (HasVar x t) -> ([x := tx] t) = t.
Proof.
  intros. induction t; simpl; trivial;
  try (destruct String.string_dec; subst; trivial);
  solve
    [ rewrite IHt; eauto using not_hv_new, not_hv_load, not_hv_spawn, not_hv_fun
    | rewrite IHt1; eauto using not_hv_asg1, not_hv_call1, not_hv_seq1;
      rewrite IHt2; eauto using not_hv_asg2, not_hv_call2, not_hv_seq2
    | exfalso; eauto using HasVar
    ].
Qed.

Lemma hasvar_typing : forall Gamma x t T,
  HasVar x t ->
  Gamma x = None ->
  ~ (Gamma |-- t is T).
Proof.
  assert (forall Gamma x, Gamma x = None -> (safe Gamma) x = None).
  { unfold safe. intros * H. rewrite H. reflexivity. }
  intros * ? HGamma F. induction_type; inversion_hv; eauto.
  - rewrite HGamma in *. discriminate.
  - rewrite lookup_update_neq in IHF; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* Equivalence                                                               *)
(* ------------------------------------------------------------------------- *)

Local Lemma equivalence_safe : forall Gamma1 Gamma2,
  Gamma1 === Gamma2 ->
  safe Gamma1 === safe Gamma2.
Proof.
  unfold map_equivalence, safe. intros * Heq k.
  specialize (Heq k). rewrite Heq. trivial.
Qed.

Local Lemma equivalence_typing : forall Gamma1 Gamma2 t T,
  Gamma1 === Gamma2 ->
  Gamma1 |-- t is T ->
  Gamma2 |-- t is T.
Proof.
  intros. generalize dependent Gamma2. induction_type; intros;
  eauto using type_of, equivalence_safe,
    MapEquivalence.lookup, MapEquivalence.update_equivalence.
Qed.

