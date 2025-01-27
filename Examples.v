From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Open Scope string_scope.

From Elo Require Import Core.
From Elo Require Import SyntacticProperties.
From Elo Require Import Eval.

Ltac solve_ty :=
  repeat match goal with
  | |- _ |-- <{unit                  }> is _ => eapply T_unit
  | |- _ |-- <{nat _                 }> is _ => eapply T_nat
  | |- _ |-- <{_; _                  }> is _ => eapply T_seq
  | |- _ |-- <{if _ then _ else _ end}> is _ => eapply T_if
  | |- _ |-- <{var _                 }> is _ => eapply T_var
  | |- _ |-- <{fn _ _ _              }> is _ => eapply T_fun
  | |- _ |-- <{call _ _              }> is _ => eapply T_call
  | |- _ |-- <{new _ : r&?T          }> is _ => eapply T_newR
  | |- _ |-- <{new _ : x&?T          }> is _ => eapply T_newX
  | |- _ |-- <{new _ : w&?T          }> is _ => eapply T_newW
  | |- _ |-- <{_ := _                }> is _ => eapply T_asg
  | |- _ |-- <{acq _ _ _             }> is _ => eapply T_acq
  | |- _ |-- <{reacq _               }> is _ => eapply T_reacq
  | |- _ |-- <{spawn _               }> is _ => eapply T_spawn
  end.

Local Ltac solve_cw :=
  repeat match goal with
  | |- consistent_waits _ <{unit                  }> => eapply cw_unit
  | |- consistent_waits _ <{nat _                 }> => eapply cw_nat
  | |- consistent_waits _ <{_ + _                 }> => eapply cw_plus
  | |- consistent_waits _ <{_ - _                 }> => eapply cw_monus
  | |- consistent_waits _ <{_; _                  }> => eapply cw_seq
  | |- consistent_waits _ <{if _ then _ else _ end}> => eapply cw_if
  | |- consistent_waits _ <{while _ do _ end      }> => eapply cw_while
  | |- consistent_waits _ <{var _                 }> => eapply cw_var
  | |- consistent_waits _ <{fn _ _ _              }> => eapply cw_fun
  | |- consistent_waits _ <{call _ _              }> => eapply cw_call
  | |- consistent_waits _ <{new _ : _             }> => eapply cw_new
  | |- consistent_waits _ <{init _ _ : _          }> => eapply cw_init
  | |- consistent_waits _ <{* _                   }> => eapply cw_load
  | |- consistent_waits _ <{_ := _                }> => eapply cw_asg
  | |- consistent_waits _ <{acq _ _ _             }> => eapply cw_acq
  | |- consistent_waits _ <{cr _ _                }> => eapply cw_cr
  | |- consistent_waits _ <{reacq _               }> => eapply cw_reacq
  | |- consistent_waits WR_self <{wait (var SELF) }> => eapply cw_wait1
  | |- consistent_waits WR_ad _ <{wait (&_ : _)   }> => eapply cw_wait2
  | |- consistent_waits _ <{reacq _               }> => eapply cw_reacq
  | |- consistent_waits _ <{spawn _               }> => eapply cw_spawn
  end.

(* ------------------------------------------------------------------------- *)
(* example 1                                                                 *)
(* ------------------------------------------------------------------------- *)

Definition example1 : tm := <{
  let "m1" : x&w&Nat = new (new (nat 3) : w&Nat) : x&w&Nat in
  let "m2" : x&w&Nat = new (new (nat 5) : w&Nat) : x&w&Nat in (
    spawn (
      acq (var "m1") "x" (
        let "result" : Nat = *(var "x") in (
          (var "x") := (nat 6);
          (var "result")
        )
      )
    );
    spawn (
      acq (var "m2") "y" (
        let "result" : Nat = *(var "y") in (
          (var "y") := (nat 10);
          (var "result")
        )
      )
    );
    (nat 20)
  )
}>.

Compute (last_result (elo nil (base example1) 200 0)).

(*
  m = (
    (Some <{&1 : (w& Nat) }>, `x&w& Nat)`, false, R_invalid) ::
    (Some <{nat 6         }>, `w&Nat    `, false, R_invalid) ::
    (Some <{&3 : (w& Nat) }>, `x&w& Nat)`, false, R_invalid) ::
    (Some <{nat 10        }>, `w&Nat    `, false, R_invalid) ::
    nil
  )

  ths = (
    <{ nat 20 }> ::
    <{ nat 3  }> ::
    <{ nat 5  }> ::
    nil
  )
*)

Lemma example1_is_well_typed :
  empty |-- example1 is `Nat`.
Proof.
  unfold example1. solve_ty.
  - unfold safe. simpl. reflexivity.
  - unfold safe. simpl. reflexivity.
  - rewrite lookup_update_eq. reflexivity.
  - eapply T_loadW. solve_ty. rewrite lookup_update_eq. reflexivity.
  - unfold safe. simpl. reflexivity.
  - rewrite lookup_update_neq; try solve [intros F; invc F].
    rewrite lookup_update_eq. reflexivity.
  - rewrite lookup_update_eq. reflexivity.
  - eapply T_loadW. solve_ty. rewrite lookup_update_eq. reflexivity.
Qed.

Lemma example1_has_consistent_waits :
  consistent_waits WR_none example1.
Proof. unfold example1. solve_cw. Qed.

(* ------------------------------------------------------------------------- *)
(* example 2                                                                 *)
(* ------------------------------------------------------------------------- *)

Notation "'V`' x" := <{var x}>
  (in custom elo_tm at level 0,
           x constr at level 0).

Notation "'N`' n" := <{nat n}>
  (in custom elo_tm at level 0,
           n constr at level 0).

Definition example2 : tm := <{
  let "bucket" : x&w&Nat = new (new (N`100) : w&Nat) : x&w&Nat in (
    spawn (
      while N`1 do
        acq V`"bucket" "n" (
          await *(V`"n");
          V`"n" := *(V`"n") + N`1
        )
      end
    );
    spawn (
      acq V`"bucket" "n" (
        V`"n" := N`555
      );
      N`1337
    )
  )
}>.

Compute (last_result (elo nil (base example2) 5000 0)).

(* gas = 10000

  ((Some <{ &1 : w&Nat }>, `x&w& Nat `, true,  R_invalid)
:: (Some <{ nat 555    }>, `w&Nat    `, false, R_invalid)
:: nil)

  (unit
:: <{
    cr 0 {
      wait &0;
      while *&1 do (wait (&0 : x&w&Nat) end);
      &1 := *&1 + 1
    };
    while 1 do
      acq &0 "n" {
        await *n;
        n := *n + 1
      }
    end
    }>
:: 1337
:: nil)

*)



(*
  let down := fn m: (x&T) {
    acq m p {
      n := *p
      while !n {
        wait cv
      }
      n := n - 1
    }
  }

  let up := fn m: (x&T) {
    acq m p {
      n := n + 1 
      broadcast cv
    }
  }

  p:
    down queroproduzir
    enter CR
      produz
    leave CR
    up queroconsumir

  c:
    down queroconsumir
    enter CR
      consume
    leave CR
    up queroproduzir
*)

