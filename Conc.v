
(* Concurrent Step *)

Inductive cstep : mem -> threads -> effect -> mem -> threads -> Prop :=
  | CST_None : forall m t ths tid,
    tid < length ths ->
    (get_th ths tid) --[EF_None]--> t ->
    m / ths ~~[EF_None]~~> m / (set ths tid t)

  | CST_Mem : forall m m' t' eff ths tid,
    tid < length ths ->
    m / (get_th ths tid) ==[eff]==> m' / t' ->
    m / ths ~~[eff]~~> m' / (set ths tid t')

  | CST_Spawn : forall m t ths th tid,
    tid < length ths ->
    (get_th ths tid) --[EF_Spawn th]--> t ->
    m / ths ~~[EF_Spawn th]~~> m / (add (set ths tid t) th)

  where "m / ths '~~[' eff ']~~>' m' / ths'" := (cstep m ths eff m' ths').

(*
Inductive smarter_cstep : mem -> threads -> trace -> mem -> threads -> Prop :=
  | CST_None : forall m t ths tid,
    ths[tid] -->+ t ->
    m / ths ~~[EF_None]~~> m / (ths[tid] := t)

  | CST_Mem : forall m m' t' eff ths tid,
    m / ths[tid] ==[tc]==> m' / t' ->
    m / ths ~~[tc]~~> m' / (ths[tid] := t')

  | CST_Spawn : forall m t ths th tid,
    ths[tid] --[EF_Spawn th]--> t ->
    m / ths ~~[EF_Spawn th]~~> m / ((ths[tid] := t) ++ th)

  where "m / ths '~~[' eff ']~~>' m' / ths'" := (cstep m ths eff m' ths').
*)

