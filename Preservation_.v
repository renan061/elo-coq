From Elo Require Import Core.

Ltac simpl_forall := 
  match goal with
  | |- forall_threads _[_ <- _] _          => intros tid'; sigma; omicron
  | |- forall_threads (_[_ <- _] +++ _) _  => intros tid'; sigma; omicron
  end.

Ltac destruct_forall_program :=
  progress (repeat (
    match goal with H : forall_program _ _ _ |- _ => destruct H end
  )).

Ltac split_preservation := 
  intros;
  match goal with
  (* vad | ctr | ss *)
  | H : forall_program ?m1 ?ths1 (?P ?m1),
    _ : ?m1 / ?ths1 ~~[_, _]~~> ?m2 / ?ths2
     |- forall_program ?m2 ?ths2 (?P ?m2) =>
    destruct_forall_program;
    invc_cstep; try invc_mstep; trivial; split; try simpl_forall; trivial
  end.
