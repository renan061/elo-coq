From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-reacqs                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
  (!!!) no-reacqs is an initial condition.
*)
Inductive no_reacqs : tm -> Prop :=
  | noreacqs_unit  :                  no_reacqs <{unit                     }>
  | noreacqs_nat   : forall n,        no_reacqs <{nat n                    }>
  | noreacqs_plus  : forall t1 t2,    no_reacqs t1 ->
                                      no_reacqs t2 ->
                                      no_reacqs <{t1 + t2                  }>
  | noreacqs_monus : forall t1 t2,    no_reacqs t1 ->
                                      no_reacqs t2 ->
                                      no_reacqs <{t1 - t2                  }>
  | noreacqs_seq   : forall t1 t2,    no_reacqs t1 ->
                                      no_reacqs t2 ->
                                      no_reacqs <{t1; t2                   }>
  | noreacqs_if    : forall t1 t2 t3, no_reacqs t1 ->
                                      no_reacqs t2 ->
                                      no_reacqs t3 ->
                                      no_reacqs <{if t1 then t2 else t3 end}>
  | noreacqs_while : forall t1 t2,    no_reacqs t1 ->
                                      no_reacqs t2 ->
                                      no_reacqs <{while t1 do t2 end       }>
  | noreacqs_var   : forall x,        no_reacqs <{var x                    }>
  | noreacqs_fun   : forall x Tx t,   no_reacqs t  ->
                                      no_reacqs <{fn x Tx t                }>
  | noreacqs_call  : forall t1 t2,    no_reacqs t1 ->
                                      no_reacqs t2 ->
                                      no_reacqs <{call t1 t2               }>
  | noreacqs_ref   : forall ad T,     no_reacqs <{&ad : T                  }>
  | noreacqs_new   : forall t T,      no_reacqs t  ->
                                      no_reacqs <{new t : T                }>
  | noreacqs_init  : forall ad t T,   no_reacqs t  ->
                                      no_reacqs <{init ad t : T            }>
  | noreacqs_load  : forall t,        no_reacqs t  ->
                                      no_reacqs <{*t                       }>
  | noreacqs_asg   : forall t1 t2,    no_reacqs t1 ->
                                      no_reacqs t2 ->
                                      no_reacqs <{t1 := t2                 }>
  | noreacqs_acq   : forall t1 x t2,  no_reacqs t1 ->
                                      no_reacqs t2 ->
                                      no_reacqs <{acq t1 x t2              }>
  | noreacqs_cr    : forall ad t,     no_reacqs t  ->
                                      no_reacqs <{cr ad t                  }>
  | noreacqs_wait  : forall t,        no_reacqs t  ->
                                      no_reacqs <{wait t                   }>
  | noreacqs_spawn : forall t,        no_reacqs t  ->
                                      no_reacqs <{spawn t                  }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _noreacqs tt :=
  match goal with
  | H : no_reacqs <{unit                  }> |- _ => clear H
  | H : no_reacqs <{nat _                 }> |- _ => clear H
  | H : no_reacqs <{_ + _                 }> |- _ => tt H
  | H : no_reacqs <{_ - _                 }> |- _ => tt H
  | H : no_reacqs <{_; _                  }> |- _ => tt H
  | H : no_reacqs <{if _ then _ else _ end}> |- _ => tt H
  | H : no_reacqs <{while _ do _ end      }> |- _ => tt H
  | H : no_reacqs <{var _                 }> |- _ => clear H
  | H : no_reacqs <{fn _ _ _              }> |- _ => tt H
  | H : no_reacqs <{call _ _              }> |- _ => tt H
  | H : no_reacqs <{&_ : _                }> |- _ => clear H
  | H : no_reacqs <{new _ : _             }> |- _ => tt H
  | H : no_reacqs <{init _ _ : _          }> |- _ => tt H
  | H : no_reacqs <{* _                   }> |- _ => tt H
  | H : no_reacqs <{_ := _                }> |- _ => tt H
  | H : no_reacqs <{acq _ _ _             }> |- _ => tt H
  | H : no_reacqs <{cr _ _                }> |- _ => tt H
  | H : no_reacqs <{wait _                }> |- _ => tt H
  | H : no_reacqs <{reacq _               }> |- _ => invc H
  | H : no_reacqs <{spawn _               }> |- _ => tt H
  end.

Ltac inv_noreacqs  := _noreacqs inv.
Ltac invc_noreacqs := _noreacqs invc.

(* decidability ------------------------------------------------------------ *)

Lemma noreacqs_dec : forall t,
  Decidable.decidable (no_reacqs t).
Proof.
  unfold Decidable.decidable. unfold not. intros.
  induction t; auto using no_reacqs;
  try (destruct IHt1, IHt2, IHt3 || destruct IHt1, IHt2 || destruct IHt);
  auto using no_reacqs;
  right; intros; invc_noreacqs; auto.
Qed.

