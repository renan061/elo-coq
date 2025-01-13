From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Open Scope string_scope.

From Elo Require Import Core.
From Elo Require Import Eval.

(*


  tm_condwait   : list thread_id -> tm
  tm_newcondvar : tm (* retorna um endereço pra tm_condwait *)
  tm_broadcast  : tm -> tm
  tm_wait       : tm -> tm

  let down := fn m: (x&T) {
    acq m p {
      n := *p
      while !n {
        wait cv
      }
      n := n - 1
    }
  }


  xpto ad --[e_reacq ad]--> unit


  let up := fn m: (x&T) {
    acq m p {
      n := n + 1 
      broadcast cv
    }
  }







  wait a x ~~[tid, e_wait]~~>


  while (!C) {
   wait cv
  }

  signal cv
  broadcast cv


  wait-for-in C cv =
    while (!C) {
      rel
      wait
      acq
    }



  queroproduzir, queroconsumir

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



(*
  let m1 = new monitor(new w&Nat 3);
  let m2 = new monitor(new w&Nat 5);
  spawn {
    acq m1 x {
      let result = *x
      x := 6
      result
    }
  }
  spawn {
    acq m2 y {
      let result = *y
      x := 10
      result
    }
  }
  20


  let m = new mon
  acq m x {
    ...
    spawn {
      acq m y {
        ...
      }
    }
  }

*)

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

Compute (last_result (evals nil (base example1) 200 0)).
(*
  m = (
    [0]: (Some <{&1 : (w& Nat)}>, `x& (w& Nat) `, false, R_invalid) ::
    [1]: (Some <{nat 6        }>, `w& Nat      `, false, R_invalid) ::
    [2]: (Some <{&3 : (w& Nat)}>, `x& (w& Nat) `, false, R_invalid) ::
    [3]: (Some <{nat 10       }>, `w& Nat      `, false, R_invalid) ::
         nil
  )
  ths = (
    [0]: <{nat 20 }> ::
    [1]: <{nat 3  }> ::
    [2]: <{nat 5  }> ::
         nil
  )
  s = "out of gas"
*)

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
  | |- _ |-- <{spawn _               }> is _ => eapply T_spawn
  end.

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

Lemma example1_reduces_correctly : forall m ths,
  m = (
    (Some <{nat 6     }>, `w&Nat`,   false, R_ad  1) ::
    (Some <{&0 : w&Nat}>, `x&w&Nat`, false, R_tid 0) ::
    (Some <{nat 10    }>, `w&Nat`,   false, R_ad  3) ::
    (Some <{&2 : w&Nat}>, `x&w&Nat`, false, R_tid 0) ::
    nil) -> 
  ths = (
    <{nat 6 }> ::
    <{nat 10}> ::
    <{nat 20}> ::
    nil) ->
  exists tc, nil \ (base example1) ~~[tc]~~>* m \ ths.
Proof.
  unfold base. intros. eexists.
  eapply multistep_trans.
Abort.




(*



spawn {

  while ? {
    block
  }

}








*)
