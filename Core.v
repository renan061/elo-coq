From Coq Require Import Arith.
From Coq Require Import Strings.String.
From Coq Require Import List.
From Coq Require Import Lia.

From Elo Require Import Util.
From Elo Require Import Array.
From Elo Require Import Map.
 
Definition id := string.
Definition num := nat.

(* ------------------------------------------------------------------------- *)
(* types                                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive immutable_typ : Set :=
  | TY_Unit
  | TY_Num
  | TY_RefI : immutable_typ -> immutable_typ
  .

Inductive typ : Set :=
  | TY_Immut : immutable_typ -> typ
  | TY_RefM : typ -> typ
  | TY_Fun : typ -> typ -> typ
  .

Definition safe (Gamma : map typ) : map typ :=
  fun k => 
    match Gamma k with
    | None => None
    | Some (TY_Immut T) => Some (TY_Immut T)
    | Some _ => None
    end.

(* ------------------------------------------------------------------------- *)
(* terms                                                                     *)
(* ------------------------------------------------------------------------- *)

Inductive tm : Set :=
  (* primitives *)
  | TM_Unit
  | TM_Num   : num -> tm
  (* memory *)
  | TM_Ref   : typ -> num -> tm
  | TM_New   : typ -> tm  -> tm
  | TM_Load  : tm  -> tm
  | TM_Asg   : tm  -> tm  -> tm
  (* functions *)
  | TM_Var   : id  -> tm
  | TM_Fun   : id  -> typ -> tm -> tm
  | TM_Call  : tm  -> tm  -> tm
  (* sequencing *)
  | TM_Seq   : tm  -> tm  -> tm
  (* concurrency *)
  | TM_Spawn : tm  -> tm
  .

(* ------------------------------------------------------------------------- *)
(* notations                                                                 *)
(* ------------------------------------------------------------------------- *)

Declare Custom Entry elo_typ.
Notation "<{{ T }}>" := T (T custom elo_typ at level 99).
Notation "( x )"     := x (in custom elo_typ, x at level 99).
Notation "x"         := x (in custom elo_typ at level 0, x constr at level 0).

Notation "'Unit'"      := (TY_Immut TY_Unit)     (in custom elo_typ at level 0).
Notation "'Num'"       := (TY_Immut TY_Num)      (in custom elo_typ at level 0).
Notation "'Immut' T"   := (TY_Immut T)           (in custom elo_typ at level 5).
Notation "'&' T"       := (TY_RefM T)            (in custom elo_typ at level 5).
Notation "'i&' T"      := (TY_Immut (TY_RefI T)) (in custom elo_typ at level 5).
Notation "T1 '-->' T2" := (TY_Fun T1 T2)         (in custom elo_typ at level 50,
                                                           right associativity).

Declare Custom Entry elo.
Notation "<{ t }>" := t (t custom elo at level 99).
Notation "x"       := x (in custom elo at level 0, x constr at level 0).

Notation "'unit'"            := (TM_Unit)       (in custom elo at level 0).
Notation "'N' n"             := (TM_Num n)      (in custom elo at level 0).
Notation "'&' ad '::' T"     := (TM_Ref T ad)    (in custom elo at level 0,
                                              T custom elo_typ at level 0).
Notation "'new' T t"         := (TM_New T t)     (in custom elo at level 0,
                                              T custom elo_typ at level 0).
Notation "'*' t"             := (TM_Load t)     (in custom elo at level 0).
Notation "t1 '=' t2"         := (TM_Asg t1 t2)  (in custom elo at level 70,
                                                         no associativity).
Notation "'var' x"           := (TM_Var x)      (in custom elo at level 0).
Notation "'fn' x Tx '-->' t" := (TM_Fun x Tx t)  (in custom elo at level 0,
                                                       x constr at level 0,
                                             Tx custom elo_typ at level 0).
Notation "'call' t1 t2"      := (TM_Call t1 t2) (in custom elo at level 0).
Notation "t1 ';' t2"         := (TM_Seq t1 t2)   (in custom elo at level 2,
                                                      right associativity).
Notation "'spawn' t"         := (TM_Spawn t)    (in custom elo at level 0).

Reserved Notation "'[' x ':=' tx ']' t"
  (at level 20, x constr).
Reserved Notation "t '--[' eff ']-->' t'"
  (at level 40, eff at next level, t' at next level).
Reserved Notation "m / t '==[' eff ']==>' m' / t'"
  (at level 40, t at next level, eff at next level, m' at next level).
Reserved Notation "m / ths '~~[' tid , eff ']~~>' m' / ths'"
  (at level 40, ths at next level, tid at next level, eff at next level,
                m' at next level).
Reserved Notation "m / t '~~[' tc ']~~>*' m' / t'"
  (at level 40, t at next level, tc at next level,
                m' at next level, t' at next level).
Reserved Notation "Gamma '|--' t 'is' T"
  (at level 40).

(* ------------------------------------------------------------------------- *)
(* values                                                                    *)
(* ------------------------------------------------------------------------- *)

Inductive value : tm -> Prop :=
  | V_Unit : value <{ unit }> 
  | V_Num : forall n, value <{ N n }>
  | V_Ref : forall ad T, value <{ &ad :: T }>
  | V_Fun : forall x Tx t, value <{ fn x Tx --> t }>
  .

(* ------------------------------------------------------------------------- *)
(* effects                                                                   *)
(* ------------------------------------------------------------------------- *)

Definition addr := nat.

Inductive effect : Set :=
  | EF_None
  | EF_Alloc (ad : addr) (v : tm) (V : typ)
  | EF_Read  (ad : addr) (v : tm)
  | EF_Write (ad : addr) (v : tm) (V : typ)
  | EF_Spawn (t : tm)
  .

(* ------------------------------------------------------------------------- *)
(* substitution                                                              *)
(* ------------------------------------------------------------------------- *)

Local Infix "=?" := string_dec (at level 70, no associativity).

Fixpoint subst (x : id) (tx t : tm) : tm :=
  match t with
  | <{ unit            }> => t
  | <{ N _             }> => t
  | <{ & _ :: _        }> => t
  | <{ new T t'        }> => <{ new T ([x := tx] t')            }>
  | <{ *t'             }> => <{ * ([x := tx] t')                }>
  | <{ t1 = t2         }> => <{ ([x := tx] t1) = ([x := tx] t2) }>
  | <{ var x'          }> => if x =? x' then tx else t
  | <{ fn x' Tx --> t' }> => if x =? x'
                              then t 
                              else <{ fn x' Tx --> ([x := tx] t')  }>
  | <{ call t1 t2      }> => <{ call ([x := tx] t1) ([x := tx] t2) }>
  | <{ t1; t2          }> => <{ ([x := tx] t1) ; ([x := tx] t2)    }>
  | <{ spawn t'        }> => <{ spawn ([x := tx] t')               }>
  end
  where "'[' x ':=' tx ']' t" := (subst x tx t).

(* ------------------------------------------------------------------------- *)
(* operational semantics -- term step                                        *)
(* ------------------------------------------------------------------------- *)

Inductive step : tm -> effect -> tm -> Prop :=
  (* New *)
  | ST_New1 : forall t t' eff T,
    t --[eff]--> t' ->
    <{ new T t }> --[eff]--> <{ new T t' }>

  | ST_New : forall ad v Tr,
    value v ->
    <{ new Tr v }> --[EF_Alloc ad v Tr]--> <{ &ad :: Tr }>

  (* Load *)
  | ST_Load1 : forall t t' eff,
    t --[eff]--> t' ->
    <{ *t }> --[eff]--> <{ *t' }>

  | ST_Load : forall ad t Tr,
    <{ * &ad :: Tr }> --[EF_Read ad t]--> t

  (* Asg *)
  | ST_Asg1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    <{ t1 = t2 }> --[eff]--> <{ t1' = t2 }>

  | ST_Asg2 : forall t t' v eff,
    value v ->
    t --[eff]--> t' ->
    <{ v = t }> --[eff]--> <{ v = t' }>

  | ST_Asg : forall ad v Tr,
    value v ->
    <{ &ad :: Tr = v }> --[EF_Write ad v Tr]--> <{ unit }>

  (* Call *)
  | ST_Call1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    <{ call t1 t2 }> --[eff]--> <{ call t1' t2 }>

  | ST_Call2 : forall t t' v eff,
    value v ->
    t --[eff]--> t' ->
    <{ call v t }> --[eff]--> <{ call v t' }>

  | ST_Call : forall x Tx t v,
    value v ->
    <{ call <{ fn x Tx --> t }> v }> --[EF_None]--> ([x := v] t)

  (* Seq *)
  | ST_Seq1 : forall t1 t1' t2 eff,
    t1 --[eff]--> t1' ->
    <{ t1; t2 }> --[eff]--> <{ t1'; t2 }>

  | ST_Seq : forall v t,
    value v ->
    <{ v; t }> --[EF_None]--> t

  (* Spawn *)
  | ST_Spawn : forall t,
    <{ spawn t }> --[EF_Spawn t]--> <{ unit }>

  where "t '--[' eff ']-->' t'" := (step t eff t').

(* ------------------------------------------------------------------------- *)
(* operational semantics -- memory step                                      *)
(* ------------------------------------------------------------------------- *)

Definition mem := list (tm * typ).
Definition memory_default := (<{ unit }>, <{{ Unit }}>).

Notation " l '[' i '].tm' " := (fst (get memory_default l i))
  (at level 9, i at next level).
Notation " l '[' i '].typ' " := (snd (get memory_default l i))
  (at level 9, i at next level).

Inductive mstep : mem -> tm -> effect -> mem -> tm -> Prop :=
  | MST_None : forall m t t',
    t --[EF_None]--> t' ->
    m / t ==[EF_None]==> m / t'

  | MST_Alloc : forall m t t' ad v Tr,
    ad = #m ->
    t --[EF_Alloc ad v Tr]--> t' ->
    m / t ==[EF_Alloc ad v Tr]==> (m +++ (v, Tr)) / t'

  | MST_Read : forall m t t' ad,
    ad < #m ->
    t --[EF_Read ad m[ad].tm]--> t' ->
    m / t ==[EF_Read ad m[ad].tm]==> m / t'

  | MST_Write : forall m t t' ad v Tr,
    ad < #m ->
    t --[EF_Write ad v Tr]--> t' ->
    m / t ==[EF_Write ad v Tr]==> m[ad <- (v, Tr)] / t'

  where "m / t '==[' eff ']==>' m' / t'" := (mstep m t eff m' t').

(* ------------------------------------------------------------------------- *)
(* operation semantics -- concurrent step                                    *)
(* ------------------------------------------------------------------------- *)

Definition threads := list tm.
Definition thread_default := <{ unit }>.

Notation " l '[' i ']' " := (l[i] or thread_default)
  (at level 9, i at next level).

Inductive cstep : mem -> threads -> nat -> effect -> mem -> threads -> Prop :=
  | CST_Mem : forall m m' t' ths tid eff,
      tid < #ths ->
      m / ths[tid] ==[eff]==> m' / t' ->
      m / ths ~~[tid, eff]~~> m' / ths[tid <- t']

  | CST_Spawn : forall m t' ths tid block,
      tid < #ths ->
      ths[tid] --[EF_Spawn block]--> t' ->
      m / ths ~~[tid, EF_Spawn block]~~> m / (ths[tid <- t'] +++ block)

  where "m / ths '~~[' tid ,  eff ']~~>' m' / ths'" :=
    (cstep m ths tid eff m' ths').

(* ------------------------------------------------------------------------- *)
(* multistep                                                                 *)
(* ------------------------------------------------------------------------- *)

Definition trace := list (nat * effect).

Inductive multistep : mem -> threads -> trace -> mem -> threads -> Prop :=
  | cmultistep_refl: forall m ths,
    m / ths ~~[nil]~~>* m / ths

  | cmultistep_trans : forall m m' m'' ths ths' ths'' tc tid eff,
    m  / ths  ~~[tc]~~>* m'  / ths'  ->
    m' / ths' ~~[tid, eff]~~> m'' / ths'' ->
    m  / ths  ~~[(tid, eff) :: tc]~~>* m'' / ths''

  where "m / t '~~[' tc ']~~>*' m' / t'" := (multistep m t tc m' t').

(* ------------------------------------------------------------------------- *)
(* typing                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition ctx := map typ.

Inductive well_typed_term : ctx -> tm -> typ -> Prop :=
  | T_Unit : forall Gamma,
    Gamma |-- <{ unit }> is <{{ Unit }}>

  | T_Num : forall Gamma n,
    Gamma |-- <{ N n }> is <{{ Num }}>

  | T_RefM : forall Gamma ad T,
    Gamma |-- <{ &ad :: &T }> is <{{ &T }}>

  | T_RefI : forall Gamma ad T,
    Gamma |-- <{ &ad :: i&T }> is <{{ i&T }}>

  | T_NewM : forall Gamma t T,
    Gamma |-- t is T ->
    Gamma |-- <{ new &T t }> is <{{ &T }}>

  | T_NewI : forall Gamma t T,
    Gamma |-- t is <{{ Immut T }}> ->
    Gamma |-- <{ new i&T t }> is <{{ i&T }}>

  | T_LoadM : forall Gamma t T,
    Gamma |-- t is <{{ &T }}> ->
    Gamma |-- <{ *t }> is T

  | T_LoadI : forall Gamma t T,
    Gamma |-- t is <{{ i&T }}> ->
    Gamma |-- <{ *t }> is <{{ Immut T }}>

  | T_Asg : forall Gamma t1 t2 T,
    Gamma |-- t1 is <{{ &T }}> ->
    Gamma |-- t2 is T ->
    Gamma |-- <{ t1 = t2 }> is <{{ Unit }}>

  | T_Var : forall Gamma x T,
    Gamma x = Some T ->
    Gamma |-- <{ var x }> is T

  | T_Fun : forall Gamma x t T Tx,
    Gamma[x <== Tx] |-- t is T ->
    Gamma |-- <{ fn x Tx --> t }> is <{{ Tx --> T }}>

  | T_Call : forall Gamma t1 t2 Tx T,
    Gamma |-- t1 is <{{ Tx --> T }}> ->
    Gamma |-- t2 is Tx ->
    Gamma |-- <{ call t1 t2 }> is T

  | T_Seq : forall Gamma t1 t2 T1 T2,
    Gamma |-- t1 is T1 ->
    Gamma |-- t2 is T2 ->
    Gamma |-- <{ t1; t2 }> is T2

  | T_Spawn : forall Gamma t T,
    safe Gamma |-- t is T ->
    Gamma |-- <{ spawn t }> is <{{ Unit }}> 

  where "Gamma '|--' t 'is' T" := (well_typed_term Gamma t T).

(* ------------------------------------------------------------------------- *)
(* decidability                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem immutable_typ_eq_dec : forall (T1 T2 : immutable_typ),
  {T1 = T2} + {T1 <> T2}.
Proof. intros. decide equality; eauto. Qed.

Theorem typ_eq_dec : forall (T1 T2 : typ),
  {T1 = T2} + {T1 <> T2}.
Proof. intros. decide equality; eauto using immutable_typ_eq_dec. Qed.

Theorem tm_eq_dec : forall (t1 t2 : tm),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros. decide equality; 
  eauto using PeanoNat.Nat.eq_dec, string_dec, typ_eq_dec.
Qed.

Theorem effect_eq_dec : forall (e1 e2 : effect),
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros. decide equality;
  eauto using PeanoNat.Nat.eq_dec, tm_eq_dec, typ_eq_dec.
Qed.

(* ------------------------------------------------------------------------- *)
(* array properties                                                          *)
(* ------------------------------------------------------------------------- *)

Definition forall_memory (m : mem) P : Prop :=
  forall_array memory_default (fun tT => P (fst tT)) m.

Definition forall_threads (ths : threads) P : Prop :=
  forall_array thread_default P ths.

Definition forall_program (m : mem) (ths : threads) P : Prop :=
  (forall_memory m P) /\ (forall_threads ths P).

Definition well_typed := fun t => exists T, empty |-- t is T.

Global Hint Unfold forall_program : core.

(* ------------------------------------------------------------------------- *)
(* determinism                                                               *)
(* ------------------------------------------------------------------------- *)

Lemma deterministic_typing : forall Gamma t T1 T2,
  Gamma |-- t is T1 ->
  Gamma |-- t is T2 ->
  T1 = T2.
Proof.
  intros * Htype1. generalize dependent T2.
  induction Htype1; intros ? Htype2;
  inversion Htype2; subst; eauto;
  repeat match goal with
  | IH : forall _, _ |-- ?t is _ -> _, H : _ |-- ?t is _ |- _ =>
    eapply IH in H; subst
  end;
  congruence.
Qed.

Ltac apply_deterministic_typing :=
  match goal with
  | H1 : _ |-- ?t is ?T1, H2 : _ |-- ?t is ?T2 |- _ =>
    assert (Heq : T1 = T2) by eauto using deterministic_typing; subst;
    try (inversion Heq; subst; clear Heq)
  end.

(* ------------------------------------------------------------------------- *)
(* auxiliary tactics                                                         *)
(* ------------------------------------------------------------------------- *)

Ltac induction_step :=
  match goal with
  | H : _ --[?e]--> _ |- _ =>
    remember e as eff; induction H; inversion Heqeff; subst
  end.

Ltac inversion_step :=
  match goal with
  | H : _ --[_]--> _ |- _ => inversion H; subst; clear H
  end.

Ltac inversion_mstep :=
  match goal with
  | H : _ / _ ==[_]==> _ / _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_mstep :=
  match goal with
  | H : _ / _ ==[_]==> _ / _ |- _ => inversion_subst_clear H
  end.

Ltac inversion_cstep :=
  match goal with
  | H : _ / _ ~~[_, _]~~> _ / _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_cstep :=
  match goal with
  | H : _ / _ ~~[_, _]~~> _ / _ |- _ => inversion_subst_clear H
  end.

Ltac inversion_multistep :=
  match goal with
  | H : _ / _ ~~[_]~~>* _ / _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_multistep :=
  match goal with
  | H : _ / _ ~~[_]~~>* _ / _ |- _ => inversion_subst_clear H
  end.

Ltac induction_type :=
  match goal with
  | H : _ |-- _ is _ |- _ => induction H
  end.

Ltac inversion_type :=
  match goal with
  | H : _ |-- <{ unit         }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ N _          }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ & _ :: _     }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ new _ _      }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ * _          }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ _ = _        }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ var _        }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ fn _ _ --> _ }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ call _ _     }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ _ ; _        }> is _ |- _ => inversion H; subst
  | H : _ |-- <{ spawn _      }> is _ |- _ => inversion H; subst
  end.

Ltac inversion_clear_type :=
  match goal with
  | H : _ |-- <{ unit         }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ N _          }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ & _ :: _     }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ new _ _      }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ * _          }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ _ = _        }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ var _        }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ fn _ _ --> _ }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ call _ _     }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ _ ; _        }> is _ |- _ => inversion_subst_clear H
  | H : _ |-- <{ spawn _      }> is _ |- _ => inversion_subst_clear H
  end.

(* ------------------------------------------------------------------------- *)
(* meta                                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma cstep_preservation :
  forall (P : mem -> tm -> Prop) m m' ths ths' tid eff,
    (* Memory step preserves the property. *)
    (forall tid' t',
      m / ths[tid'] ==[eff]==> m' / t' ->
      P m' t'
    ) ->
    (* The untouched threads and the new memory still preserve the property. *)
    (forall tid' t',
      tid <> tid' ->
      tid' < #ths ->
      m / ths[tid] ==[eff]==> m' / t' ->
      P m' ths[tid']
    ) ->
    (* The new thread preserves the property. *)
    (forall block t',
      ths[tid] --[EF_Spawn block]--> t' ->
      P m block
    ) ->
    (* The term after the spawn preserves the property. *)
    (forall block t',
      ths[tid] --[EF_Spawn block]--> t' ->
      P m t' 
    ) ->
    (* Unit preserves the property. *)
    P m' thread_default ->
    (* What we want to prove. *)
    forall_threads ths (P m) ->
    m / ths ~~[tid, eff]~~> m' / ths' ->
    forall_threads ths' (P m').
Proof.
  intros. inversion_cstep; intros tid'.
  - destruct (Nat.eq_dec tid tid'); subst; simpl_array; eauto.
    decompose sum (lt_eq_lt_dec tid' (#ths)); subst; eauto;
    simpl_array; eauto.
  - destruct (Nat.eq_dec tid' (#ths)); subst.
    + rewrite <- (set_preserves_length _ tid t'). simpl_array. eauto.
    + destruct (lt_eq_lt_dec tid' (length ths)) as [[Ha | ?] | Hb]; subst;
      try lia.
      * rewrite <- (set_preserves_length _ tid t') in Ha. simpl_array.
        destruct (Nat.eq_dec tid tid'); subst; simpl_array; eauto.
      * rewrite <- (set_preserves_length _ tid t') in Hb. simpl_array. eauto.
Qed.

