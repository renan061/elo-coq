From Elo Require Import Util.
From Elo Require Import Sem.
From Elo Require Import SemExt.

(* ------------------------------------------------------------------------- *)
(* kappa                                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma gcr_rewrite_seq_t1 : forall t1 t2 R,
  ~ value t1 ->
  gcr <{t1; t2}> R = gcr t1 R.
Proof.
  intros * H. simpl. destruct t1; auto; exfalso; auto using value.
Qed.

Lemma gcr_rewrite_seq_t2 : forall t1 t2 R,
  value t1 ->
  gcr <{t1; t2}> R = gcr t2 R.
Proof.
  intros * H. simpl. destruct t1; auto; invc H.
Qed.

Lemma gcr_rewrite_call_t1 : forall t1 t2 R,
  ~ value t1 ->
  gcr <{call t1 t2}> R = gcr t1 R.
Proof.
  intros * H. simpl. destruct t1; auto; exfalso; auto using value.
Qed.

Lemma gcr_rewrite_call_t2 : forall t1 t2 R,
  value t1 ->
  gcr <{call t1 t2}> R = gcr t2 R.
Proof.
  intros * H. simpl. destruct t1; auto; invc H.
Qed.

Lemma gcr_rewrite_initX : forall ad t T R,
  gcr <{init ad t : x&T}> R = gcr t (R_ad ad).
Proof. trivial. Qed.

Lemma gcr_rewrite_initW : forall ad t T R,
  gcr <{init ad t : w&T}> R = gcr t R.
Proof. trivial. Qed.

Lemma gcr_rewrite_asg_t1 : forall t1 t2 R,
  ~ value t1 ->
  gcr <{t1 := t2}> R = gcr t1 R.
Proof.
  intros * H. simpl. destruct t1; auto; exfalso; auto using value.
Qed.

Lemma gcr_rewrite_asg_t2 : forall t1 t2 R,
  value t1 ->
  gcr <{t1 := t2}> R = gcr t2 R.
Proof.
  intros * H. simpl. destruct t1; auto; invc H.
Qed.

(* gcr (get-current-region) simplification *)
Ltac kappa :=
 repeat match goal with
 | H : context C [ gcr <{?t1; ?t2    }> ?R ], H' : ~ value ?t1 |- _ =>
   rewrite (gcr_rewrite_seq_t1 t1 t2 R H') in H
 | H : context C [ gcr <{?t1; ?t2    }> ?R ], H' : value   ?t1 |- _ =>
   rewrite (gcr_rewrite_seq_t2 t1 t2 R H') in H
 | H : context C [ gcr <{call ?t1 ?t2}> ?R ], H' : ~ value ?t1 |- _ =>
   rewrite (gcr_rewrite_call_t1 t1 t2 R H') in H
 | H : context C [ gcr <{call ?t1 ?t2}> ?R ], H' : value   ?t1 |- _ =>
   rewrite (gcr_rewrite_call_t2 t1 t2 R H') in H
 | H : context C [ gcr <{?t1 := ?t2  }> ?R ], H' : ~ value ?t1 |- _ =>
   rewrite (gcr_rewrite_asg_t1 t1 t2 R H') in H
 | H : context C [ gcr <{?t1 := ?t2  }> ?R ], H' : value   ?t1 |- _ =>
   rewrite (gcr_rewrite_asg_t2 t1 t2 R H') in H

 | H : context C [gcr <{unit                }> _] |- _ => simpl in H
 | H : context C [gcr <{nat _               }> _] |- _ => simpl in H
 | H : context C [gcr <{?t; _               }> _] |- _ => destruct (value_dec t)
 | H : context C [gcr <{var _               }> _] |- _ => simpl in H
 | H : context C [gcr <{fn _ _ _            }> _] |- _ => simpl in H
 | H : context C [gcr <{call ?t _           }> _] |- _ => destruct (value_dec t)
 | H : context C [gcr <{& _ : _             }> _] |- _ => simpl in H
 | H : context C [gcr <{new _ : _           }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : Unit     }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : Nat      }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : r&_      }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : x&_      }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : w&_      }> _] |- _ => simpl in H
 | H : context C [gcr <{init _ _ : (_ --> _)}> _] |- _ => simpl in H 
 | H : context C [gcr <{init _ _ : Safe ?T  }> _] |- _ => destruct T 
 | H : context C [gcr <{init _ _ : ?T       }> _] |- _ => destruct T 
 | H : context C [gcr <{* _                 }> _] |- _ => simpl in H
 | H : context C [gcr <{?t := _             }> _] |- _ => destruct (value_dec t)
 | H : context C [gcr <{acq _ _ _           }> _] |- _ => simpl in H
 | H : context C [gcr <{cr _ _              }> _] |- _ => simpl in H
 | H : context C [gcr <{spawn _             }> _] |- _ => simpl in H

 | H' : ~ value ?t1 |- context C [ gcr <{?t1; ?t2    }> ?R ] =>
   rewrite (gcr_rewrite_seq_t1 t1 t2 R H')
 | H' : value   ?t1 |- context C [ gcr <{?t1; ?t2    }> ?R ] =>
   rewrite (gcr_rewrite_seq_t2 t1 t2 R H')
 | H' : ~ value ?t1 |- context C [ gcr <{call ?t1 ?t2}> ?R ] =>
   rewrite (gcr_rewrite_call_t1 t1 t2 R H')
 | H' : value   ?t1 |- context C [ gcr <{call ?t1 ?t2}> ?R ] =>
   rewrite (gcr_rewrite_call_t2 t1 t2 R H')
 | H' : ~ value ?t1 |- context C [ gcr <{?t1 := ?t2  }> ?R ] =>
   rewrite (gcr_rewrite_asg_t1 t1 t2 R H')
 | H' : value   ?t1 |- context C [ gcr <{?t1 := ?t2  }> ?R ] =>
   rewrite (gcr_rewrite_asg_t2 t1 t2 R H')

 | |- context C [gcr <{unit                }> _] => simpl
 | |- context C [gcr <{nat _               }> _] => simpl
 | |- context C [gcr <{?t; _               }> _] => destruct (value_dec t)
 | |- context C [gcr <{var _               }> _] => simpl
 | |- context C [gcr <{fn _ _ _            }> _] => simpl
 | |- context C [gcr <{call ?t _           }> _] => destruct (value_dec t)
 | |- context C [gcr <{& _ : _             }> _] => simpl
 | |- context C [gcr <{new _ : _           }> _] => simpl
 | |- context C [gcr <{init _ _ : Unit     }> _] => simpl
 | |- context C [gcr <{init _ _ : Nat      }> _] => simpl
 | |- context C [gcr <{init _ _ : r&_      }> _] => simpl
 | |- context C [gcr <{init _ _ : x&_      }> _] => simpl
 | |- context C [gcr <{init _ _ : w&_      }> _] => simpl
 | |- context C [gcr <{init _ _ : (_ --> _)}> _] => simpl 
 | |- context C [gcr <{init _ _ : Safe ?T  }> _] => destruct T 
 | |- context C [gcr <{init _ _ : ?T       }> _] => destruct T 
 | |- context C [gcr <{* _                 }> _] => simpl
 | |- context C [gcr <{?t := _             }> _] => destruct (value_dec t)
 | |- context C [gcr <{acq _ _ _           }> _] => simpl
 | |- context C [gcr <{cr _ _              }> _] => simpl
 | |- context C [gcr <{spawn _             }> _] => simpl
 end.

