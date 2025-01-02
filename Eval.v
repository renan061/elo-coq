From Elo Require Import Core.

Definition bind (o : option (mem * tm)) (f : tm -> tm)
  : option (mem * tm) :=
  match o with
  | Some (m, t) => Some (m, (f t))
  | None        => None
  end.

Local Notation "o '>>=' f" := (bind o f)
  (no associativity, at level 10).

Fixpoint eval (m : mem) (t : tm) : option (mem * tm) :=
  let term2 := fun
    (m : mem)
    (t1 t2 : tm)
    (cons : tm -> tm -> tm)
    (result : option (mem * tm)) =>
      if is_value t1 then
        if is_value t2 then
          result
        else
          eval m t2 >>= (fun t2' => cons t1 t2')
      else
        eval m t1 >>= (fun t1' => cons t1' t2)
  in
  match t with
  | <{unit}> => Some (m, t)
  (* --------------------------------------------------------------------- *)
  | <{nat _}> => Some (m, t)
  (* --------------------------------------------------------------------- *)
  | <{t1 + t2}> => term2 m t1 t2 tm_plus (
      match t with
      | <{nat n1 + nat n2}> => Some (m, <{nat (n1 + n2)}>)
      | _ => None
      end)
  (* --------------------------------------------------------------------- *)
  | <{t1 - t2}> => term2 m t1 t2 tm_monus (
      match t with
      | <{nat n1 - nat n2}> => Some (m, <{nat (n1 - n2)}>)
      | _ => None
      end)
  (* --------------------------------------------------------------------- *)
  | <{t1; t2}> => if is_value t1
                    then Some (m, t2)
                    else eval m t1 >>= (fun t1' => <{t1'; t2}>)
  (* --------------------------------------------------------------------- *)
  | <{if t1 then t2 else t3 end}> => 
    if is_value t1 then
      match t1 with
      | <{nat O    }> => Some (m, t3)
      | <{nat (S _)}> => Some (m, t2)
      | _ => None
      end
    else
      eval m t1 >>= (fun t1' => <{if t1' then t2 else t3 end}>)
  (* --------------------------------------------------------------------- *)
  | <{while t1 do t2 end}> =>
    let t' := <{if t1 then t2; while t1 do t2 end else unit end}> in
    Some (m, t')
  (* --------------------------------------------------------------------- *)
  | <{var _}> => Some (m, t)
  (* --------------------------------------------------------------------- *)
  | <{fn _ _ _}> => Some (m, t)
  (* --------------------------------------------------------------------- *)
  | <{call t1 t2}> => term2 m t1 t2 tm_call (
      match t with
      | <{call (fn x _ t) tx}> => Some (m, <{[x := tx] t}>)
      | _ => None
      end)
  (* --------------------------------------------------------------------- *)
  | <{&_ : _}> => Some (m, t)
  (* --------------------------------------------------------------------- *)
  | <{new t : T}> => None
  (* --------------------------------------------------------------------- *)
  | <{init ad t : T}> => None
  (* --------------------------------------------------------------------- *)
  | <{*t}> => None
  (* --------------------------------------------------------------------- *)
  | <{t1 := t2}> => None
  (* --------------------------------------------------------------------- *)
  | <{acq t1 x t2}> => None
  (* --------------------------------------------------------------------- *)
  | <{cr ad t}> => None
  (* --------------------------------------------------------------------- *)
  | <{spawn t}> => None
  end.















































Inductive state : Set :=
  | done    : mem  -> tm -> state
  | waiting : addr -> tm -> state
  | error   : state
  | oog     : state
  .

Definition ret (m : mem) (o : option tm) : state :=
  match o with
  | Some t => done m t
  | None   => error
  end.

Definition bind (s : state) (f : mem -> tm -> state) : state :=
  match s with
  | done m t => f m t
  | _        => s
  end.

Local Notation "m ',' t '<-' s1 ';;' s2" := (bind s1 (fun m t => s2))
  (right associativity, at level 84, t at next level, s1 at next level).

Local Notation "s1 ';;' s2" := (bind s1 (fun _ _ => s2))
  (at level 100, right associativity).

Definition eplus (t1 t2 : tm) : option tm :=
  match t1 with
  | <{nat n1}> => match t2 with
                  | <{nat n2}> => Some <{nat (n1 + n2)}>
                  | _          => None
                  end
  | _ => None
  end.

Definition emonus (t1 t2 : tm) : option tm :=
  match t1 with
  | <{nat n1}> => match t2 with
                  | <{nat n2}> => Some <{nat (n1 - n2)}>
                  | _          => None
                  end
  | _ => None
  end.

Definition eif (t1 t2 t3 : tm) : option tm :=
  match t1 with
  | <{nat O    }> => Some t3
  | <{nat (S _)}> => Some t2
  | _             => None
  end.

Definition ecall (t tx : tm) : option tm :=
  match t with
  | <{fn x _ t'}> => Some <{[x := tx]t'}>
  | _ => None
  end.

Definition eload (m : mem) (t : tm) : option tm :=
  match t with
  | <{&ad : _}> => m[ad].t
  | _           => None
  end.

Definition easg (m : mem) (t1 t2 : tm) : state :=
  match t1 with
  | <{&ad : T}> => ret m[ad.t <- t2] (Some <{unit}>)
  | _ => error
  end.

Definition eacq (m : mem) (t1 : tm) (x : id) (t2 : tm) : state :=
  match t1 with
  | <{&ad : T}> => 
    match m[ad].t with
    | Some tx =>
      if m[ad].X
        then waiting ad <{acq t1 x t2}>
        else ret m[ad.X <- true] (Some <{[x := tx]t2}>)
    | None => error
    end
  | _ => error
  end.

Fixpoint eval (m : mem) (t : tm) (i : nat) : state :=
  match i with
  | O    => oog
  | S i' =>
    match t with
    | <{unit }> => done m t
    | <{nat n}> => done m t
    (* --- *)
    | <{t1 + t2}> =>
      m',  t1' <- eval m  t1 i' ;;
      m'', t2' <- eval m' t2 i' ;;
      ret m'' (eplus t1' t2')
    | <{t1 - t2}> =>
      m',  t1' <- eval m  t1 i' ;;
      m'', t2' <- eval m' t2 i' ;;
      ret m'' (emonus t1' t2')
    | <{t1; t2}> =>
      m',  t1' <- eval m  t1 i' ;;
      m'', t2' <- eval m' t2 i' ;;
      ret m'' (Some t2')
    | <{if t1 then t2 else t3 end}> =>
      m',  t1' <- eval m  t1 i' ;;
      ret m' (eif t1' t2 t3)
    | <{while t1 do t2 end}> =>
      eval m <{if t1 then t2; while t1 do t2 end else unit end}> i'
    (* --- *)
    | <{var _     }> => error
    | <{fn _ _ _  }> => error
    | <{call t1 t2}> =>
      m',  t1' <- eval m  t1 i' ;;
      m'', t2' <- eval m' t2 i' ;;
      ret m'' (ecall t1' t2')
    (* --- *)
    | <{&_ : _   }> => error
    | <{new t : T}> =>
      let ad := #m in
      ret (m +++ (_cell None T false R_invalid)) (Some <{init ad t : T}>)
    | <{init ad t : T}> =>
      m', t' <- eval m t i' ;;
      ret m'[ad.t <- t'] (Some <{&ad : T}>)
    | <{*t}> =>
      m', t' <- eval m t i' ;;
      ret m' (eload m' t')
    | <{t1 := t2}> =>
      m',  t1' <- eval m  t1 i' ;;
      m'', t2' <- eval m' t2 i' ;;
      easg m'' t1' t2'
    | <{acq t1 x t2}> =>
      m', t1' <- eval m t1 i' ;;
      eacq m' t1' x t2
    (* --- *)
    | _ => error
    end
  end.

