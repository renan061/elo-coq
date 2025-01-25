From Elo Require Import Util.
From Elo Require Import Sem.
From Elo Require Import SemExt.

(* ------------------------------------------------------------------------- *)
(* kappa                                                                     *)
(* ------------------------------------------------------------------------- *)

Local Ltac solve_kappa_value :=
  intros t1 * H; simpl; destruct t1; auto; invc H.

Local Ltac solve_kappa_notvalue :=
  intros t1 * H; simpl; destruct t1; auto; exfalso; auto using value.

(* ------------------------------------------------------------------------- *)

Lemma kappa_plus__value : forall t1 t2 R,
  value t1   -> gcr <{t1 + t2}> R = gcr t2 R.
Proof. solve_kappa_value. Qed.

Lemma kappa_plus__notvalue : forall t1 t2 R,
  ~ value t1 -> gcr <{t1 + t2}> R = gcr t1 R.
Proof. solve_kappa_notvalue. Qed.

(* ------------------------------------------------------------------------- *)

Lemma kappa_monus__value : forall t1 t2 R,
  value t1   -> gcr <{t1 - t2}> R = gcr t2 R.
Proof. solve_kappa_value. Qed.

Lemma kappa_monus__notvalue : forall t1 t2 R,
  ~ value t1 -> gcr <{t1 - t2}> R = gcr t1 R.
Proof. solve_kappa_notvalue. Qed.

(* ------------------------------------------------------------------------- *)

Lemma kappa_call__value : forall t1 t2 R,
  value t1   -> gcr <{call t1 t2}> R = gcr t2 R.
Proof. solve_kappa_value. Qed.

Lemma kappa_call__notvalue : forall t1 t2 R,
  ~ value t1 -> gcr <{call t1 t2}> R = gcr t1 R.
Proof. solve_kappa_notvalue. Qed.

(* ------------------------------------------------------------------------- *)

Lemma kappa_initX : forall ad t T R,
  gcr <{init ad t : x&T}> R = gcr t (R_ad ad).
Proof. trivial. Qed.

Lemma kappa_initW : forall ad t T R,
  gcr <{init ad t : w&T}> R = gcr t R.
Proof. trivial. Qed.

(* ------------------------------------------------------------------------- *)

Lemma kappa_asg__value : forall t1 t2 R,
  value t1   -> gcr <{t1 := t2}> R = gcr t2 R.
Proof. solve_kappa_value. Qed.

Lemma kappa_asg__notvalue : forall t1 t2 R,
  ~ value t1 -> gcr <{t1 := t2}> R = gcr t1 R.
Proof. solve_kappa_notvalue. Qed.

(* ------------------------------------------------------------------------- *)

(* gcr (get-current-region) simplification *)
Ltac kappa :=
 repeat match goal with
 | H : context[ gcr <{?t1 + ?t2    }> ?R ],   H' : value   ?t1 |- _ =>
   rewrite (kappa_plus__value     t1 t2 R H')    in H
 | H : context[ gcr <{?t1 + ?t2    }> ?R ],   H' : ~ value ?t1 |- _ =>
   rewrite (kappa_plus__notvalue  t1 t2 R H')    in H

 | H : context[ gcr <{?t1 - ?t2    }> ?R ],   H' : value   ?t1 |- _ =>
   rewrite (kappa_monus__value    t1 t2 R H')    in H
 | H : context[ gcr <{?t1 - ?t2    }> ?R ],   H' : ~ value ?t1 |- _ =>
   rewrite (kappa_monus__notvalue t1 t2 R H')    in H

 | H : context[ gcr <{call ?t1 ?t2}> ?R ],    H' : value   ?t1 |- _ =>
   rewrite (kappa_call__value     t1 t2 R H')    in H
 | H : context[ gcr <{call ?t1 ?t2}> ?R ],    H' : ~ value ?t1 |- _ =>
   rewrite (kappa_call__notvalue  t1 t2 R H')    in H

 | H : context[ gcr <{?t1 := ?t2  }> ?R ],    H' : value   ?t1 |- _ =>
   rewrite (kappa_asg__value      t1 t2 R H')    in H
 | H : context[ gcr <{?t1 := ?t2  }> ?R ],    H' : ~ value ?t1 |- _ =>
   rewrite (kappa_asg__notvalue   t1 t2 R H')    in H

 | H : context[gcr <{unit                }> _] |- _ => simpl in H
 | H : context[gcr <{nat _               }> _] |- _ => simpl in H
 | H : context[gcr <{?t + _              }> _] |- _ => destruct (value_dec t)
 | H : context[gcr <{?t - _              }> _] |- _ => destruct (value_dec t)
 | H : context[gcr <{?t; _               }> _] |- _ => simpl in H
 | H : context[gcr (tm_if ?t _ _         )  _] |- _ => simpl in H
 | H : context[gcr (tm_while _ _         )  _] |- _ => simpl in H
 | H : context[gcr <{var _               }> _] |- _ => simpl in H
 | H : context[gcr <{fn _ _ _            }> _] |- _ => simpl in H
 | H : context[gcr <{call ?t _           }> _] |- _ => destruct (value_dec t)
 | H : context[gcr <{& _ : _             }> _] |- _ => simpl in H
 | H : context[gcr <{new _ : _           }> _] |- _ => simpl in H
 | H : context[gcr <{init _ _ : Unit     }> _] |- _ => simpl in H
 | H : context[gcr <{init _ _ : Nat      }> _] |- _ => simpl in H
 | H : context[gcr <{init _ _ : r&_      }> _] |- _ => simpl in H
 | H : context[gcr <{init _ _ : x&_      }> _] |- _ => simpl in H
 | H : context[gcr <{init _ _ : w&_      }> _] |- _ => simpl in H
 | H : context[gcr <{init _ _ : (_ --> _)}> _] |- _ => simpl in H 
 | H : context[gcr <{init _ _ : Safe ?T  }> _] |- _ => destruct T 
 | H : context[gcr <{init _ _ : ?T       }> _] |- _ => destruct T 
 | H : context[gcr <{* _                 }> _] |- _ => simpl in H
 | H : context[gcr <{?t := _             }> _] |- _ => destruct (value_dec t)
 | H : context[gcr <{acq _ _ _           }> _] |- _ => simpl in H
 | H : context[gcr <{cr _ _              }> _] |- _ => simpl in H
 | H : context[gcr <{wait _              }> _] |- _ => simpl in H
 | H : context[gcr <{reacq _             }> _] |- _ => simpl in H
 | H : context[gcr <{spawn _             }> _] |- _ => simpl in H

 | H' : value   ?t1 |- context[ gcr <{?t1 + ?t2      }> ?R ] =>
   rewrite (kappa_plus__value     t1 t2 R H')
 | H' : ~ value ?t1 |- context[ gcr <{?t1 + ?t2      }> ?R ] =>
   rewrite (kappa_plus__notvalue  t1 t2 R H')

 | H' : value   ?t1 |- context[ gcr <{?t1 - ?t2      }> ?R ] =>
   rewrite (kappa_monus__value    t1 t2 R H')
 | H' : ~ value ?t1 |- context[ gcr <{?t1 - ?t2      }> ?R ] =>
   rewrite (kappa_monus__notvalue t1 t2 R H')

 | H' : value   ?t1 |- context[ gcr <{call ?t1 ?t2   }> ?R ] =>
   rewrite (kappa_call__value     t1 t2 R H')
 | H' : ~ value ?t1 |- context[ gcr <{call ?t1 ?t2   }> ?R ] =>
   rewrite (kappa_call__notvalue  t1 t2 R H')

 | H' : value   ?t1 |- context[ gcr <{?t1 := ?t2     }> ?R ] =>
   rewrite (kappa_asg__value      t1 t2 R H')
 | H' : ~ value ?t1 |- context[ gcr <{?t1 := ?t2     }> ?R ] =>
   rewrite (kappa_asg__notvalue   t1 t2 R H')

 | |- context[gcr <{unit                }> _] => simpl
 | |- context[gcr <{nat _               }> _] => simpl
 | |- context[gcr <{?t + _              }> _] => destruct (value_dec t)
 | |- context[gcr <{?t - _              }> _] => destruct (value_dec t)
 | |- context[gcr <{?t; _               }> _] => simpl
 | |- context[gcr (tm_if ?t _ _         )  _] => simpl
 | |- context[gcr (tm_while _ _         )  _] => simpl
 | |- context[gcr <{var _               }> _] => simpl
 | |- context[gcr <{fn _ _ _            }> _] => simpl
 | |- context[gcr <{call ?t _           }> _] => destruct (value_dec t)
 | |- context[gcr <{& _ : _             }> _] => simpl
 | |- context[gcr <{new _ : _           }> _] => simpl
 | |- context[gcr <{init _ _ : Unit     }> _] => simpl
 | |- context[gcr <{init _ _ : Nat      }> _] => simpl
 | |- context[gcr <{init _ _ : r&_      }> _] => simpl
 | |- context[gcr <{init _ _ : x&_      }> _] => simpl
 | |- context[gcr <{init _ _ : w&_      }> _] => simpl
 | |- context[gcr <{init _ _ : (_ --> _)}> _] => simpl 
 | |- context[gcr <{init _ _ : Safe ?T  }> _] => destruct T 
 | |- context[gcr <{init _ _ : ?T       }> _] => destruct T 
 | |- context[gcr <{* _                 }> _] => simpl
 | |- context[gcr <{?t := _             }> _] => destruct (value_dec t)
 | |- context[gcr <{acq _ _ _           }> _] => simpl
 | |- context[gcr <{cr _ _              }> _] => simpl
 | |- context[gcr <{wait _              }> _] => simpl
 | |- context[gcr <{reacq _             }> _] => simpl
 | |- context[gcr <{spawn _             }> _] => simpl
 end.
 
