From Elo Require Import Core.

(* ------------------------------------------------------------------------- *)
(* no-wrefs                                                                  *)
(* ------------------------------------------------------------------------- *)

Inductive no_wrefs : tm -> Prop :=
  | nowrefs_unit  :                no_wrefs <{unit         }>
  | nowrefs_nat   : forall n,      no_wrefs <{nat n        }>
  | nowrefs_var   : forall x,      no_wrefs <{var x        }>
  | nowrefs_fun   : forall x Tx t, no_wrefs t  ->
                                   no_wrefs <{fn x Tx t    }>
  | nowrefs_call  : forall t1 t2,  no_wrefs t1 ->
                                   no_wrefs t2 ->
                                   no_wrefs <{call t1 t2   }>
  | nowrefs_refR  : forall ad T,   no_wrefs <{&ad : r&T    }>
  | nowrefs_refX  : forall ad T,   no_wrefs <{&ad : x&T    }>
  | nowrefs_new   : forall t T,    no_wrefs t  ->
                                   no_wrefs <{new t : T    }>
  | nowrefs_init  : forall ad t T, no_wrefs t  ->
                                   no_wrefs <{init ad t : T}>
  | nowrefs_load  : forall t,      no_wrefs t  ->
                                   no_wrefs <{*t           }>
  | nowrefs_asg   : forall t1 t2,  no_wrefs t1 ->
                                   no_wrefs t2 ->
                                   no_wrefs <{t1 := t2     }>
  | nowrefs_acq   : forall t1 t2,  no_wrefs t1 ->
                                   no_wrefs t2 ->
                                   no_wrefs <{acq t1 t2    }>
  | nowrefs_cr    : forall ad' t,  no_wrefs t  ->
                                   no_wrefs <{cr ad' t     }>
  | nowrefs_spawn : forall t,      no_wrefs t ->
                                   no_wrefs <{spawn t      }>
  .

(* inversion --------------------------------------------------------------- *)

Local Ltac _nowrefs tt :=
  match goal with
  | H : no_wrefs <{unit        }> |- _ => clear H
  | H : no_wrefs <{nat _       }> |- _ => clear H
  | H : no_wrefs <{var _       }> |- _ => clear H
  | H : no_wrefs <{fn _ _ _    }> |- _ => tt H
  | H : no_wrefs <{call _ _    }> |- _ => tt H
  | H : no_wrefs <{&_ : r&_    }> |- _ => clear H
  | H : no_wrefs <{&_ : x&_    }> |- _ => clear H
  | H : no_wrefs <{&_ : w&_    }> |- _ => inv H
  | H : no_wrefs <{new _ : _   }> |- _ => tt H
  | H : no_wrefs <{init _ _ : _}> |- _ => tt H
  | H : no_wrefs <{* _         }> |- _ => tt H
  | H : no_wrefs <{_ := _      }> |- _ => tt H
  | H : no_wrefs <{acq _ _     }> |- _ => tt H
  | H : no_wrefs <{cr _ _      }> |- _ => tt H
  | H : no_wrefs <{spawn _     }> |- _ => tt H
  end.

Ltac inv_nowrefs  := _nowrefs inv.
Ltac invc_nowrefs := _nowrefs invc.

