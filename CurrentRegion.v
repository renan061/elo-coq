From Coq Require Import List.

From Elo Require Import Core.

From Elo Require Import SyntacticProperties.

From Elo Require Import ConsistentRegions.

(* build-stack *)
Fixpoint bs (t' : tm) : stack region :=
  match t' with
  | <{unit         }> => nil
  | <{nat n        }> => nil
  | <{var x        }> => nil
  | <{fn x Tx t    }> => nil
  | <{call t1 t2   }> => if is_value t1 then bs t2 else bs t1
  | <{&ad : T      }> => nil
  | <{new t : T    }> => nil
  | <{init ad t : T}> => if is_refX T then bs t +++ R_monitor ad else bs t
  | <{*t           }> => bs t
  | <{t1 := t2     }> => if is_value t1 then bs t2 else bs t1
  | <{acq t1 x t2  }> => bs t1
  | <{cr ad t      }> => bs t +++ R_monitor ad
  | <{spawn t      }> => nil
  end.

Inductive current_region (R : region) : region -> tm -> Prop :=
  | curr_unit  :                    current_region R R  <{unit           }>
  | curr_nat   : forall n,          current_region R R  <{nat n          }>
  | curr_var   : forall x,          current_region R R  <{var x          }>

  | curr_fun   : forall x Tx t,     current_region R R  <{fn x Tx t      }>

  | curr_call1 : forall R' t1 t2,   ~ value t1             ->
                                    current_region R R' t1 ->
                                    current_region R R' <{call t1 t2     }>

  | curr_call2 : forall R' t1 t2,   value t1               ->
                                    current_region R R' t2 ->
                                    current_region R R' <{call t1 t2     }>

  | curr_ref   : forall ad T,       current_region R R  <{&ad : T        }>
  | curr_new   : forall t T,        current_region R R  <{new t : T      }>

  | curr_initR : forall R' ad t T,  current_region R R' t  ->
                                    current_region R R' <{init ad t : r&T}>

  | curr_initX : forall R' ad t T,  current_region (R_monitor ad) R' t ->
                                    current_region R R' <{init ad t : x&T}>

  | curr_initW : forall R' ad t T,  current_region R R' t  ->
                                    current_region R R' <{init ad t : w&T}>

  | curr_load  : forall R' t,       current_region R R' t  ->
                                    current_region R R' <{*t             }>

  | curr_asg1  : forall R' t1 t2,   ~ value t1             ->
                                    current_region R R' t1 ->
                                    current_region R R' <{t1 := t2       }>

  | curr_asg2  : forall R' t1 t2,   value t1               ->
                                    current_region R R' t2 ->
                                    current_region R R' <{t1 := t2       }>

  | curr_acq1  : forall R' t1 x t2, ~ value t1             ->
                                    current_region R R' t1 ->
                                    current_region R R' <{acq t1 x t2    }>

  | curr_acq2  : forall R' t1 x t2, value t1               ->
                                    current_region R R' t2 ->
                                    current_region R R' <{acq t1 x t2    }>

  | curr_cr    : forall R' ad t,    current_region (R_monitor ad) R' t ->
                                    current_region R R' <{cr ad t        }>

  | curr_spawn : forall t,          current_region R R  <{spawn t        }>
  .

Definition consistent_current_region (ths : threads) (r : regions) :=
  forall tid, current_region (R_thread tid) (regions_peek r tid) ths[tid].


Theorem 
  m1 / ths1 / o1 / r1 ~~[tid, e]~~> m2 / ths2 / o2 / r2 ->


Lemma something : forall m1 m2 ths1 ths2 o1 o2 r1 r2 tid T,
  consistent_regions o1 (R_thread tid) ths1[tid] ->
  m1 / ths1 / o1 / r1 ~~[tid, e_alloc (#m1) `w&T`]~~> m2 / ths2 / o2 / r2 ->
  current_region (R_thread tid) (o2[#o1] or R_any) ths1[tid].
Proof.
  intros. invc_ostep; try discriminate. invc_cstep. invc_mstep. sigma.
 
  repeat clean.
  clear H1. clear T0.

  ind_tstep; invc_creg; eauto using current_region.
  - assert (~ value t1) by (intros ?; value_does_not_step).
    eauto using current_region.
  - admit.

Abort.
