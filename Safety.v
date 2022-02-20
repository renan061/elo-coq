

From Elo Require Export Core.

Inductive has_access : tm -> nat -> Prop :=
  | has_access_trans : forall ad ad' m t,
    get_tm m ad = TM_Loc ad' ->
    has_access t ad ->
    has_access t ad'

  | has_access_fun : forall ad p P block R,
    has_access block ad ->
    has_access (TM_Fun p P block R) ad

  | has_access_new : forall ad t,
    has_access t ad ->
    has_access (TM_New t) ad

  | has_access_loc : forall ad,
    has_access (TM_Loc ad) ad

  | has_access_load : forall ad t,
    has_access t ad ->
    has_access (TM_Load t) ad

  | has_access_asg1 : forall ad l r,
    has_access l ad ->
    has_access (TM_Asg l r) ad

  | has_access_asg2 : forall ad l r,
    has_access r ad ->
    has_access (TM_Asg l r) ad

  | has_access_call1 : forall ad f a,
    has_access f ad ->
    has_access (TM_Call f a) ad

  | has_access_call2 : forall ad f a,
    has_access a ad ->
    has_access (TM_Call f a) ad

  | has_access_seq1 : forall ad t1 t2,
    has_access t1 ad ->
    has_access (TM_Seq t1 t2) ad

  | has_access_seq2 : forall ad t1 t2,
    has_access t2 ad ->
    has_access (TM_Seq t1 t2) ad

  | has_access_let1 : forall ad id E e t,
    has_access e ad ->
    has_access (TM_Let id E e t) ad

  | has_access_let2 : forall ad id E e t,
    has_access t ad ->
    has_access (TM_Let id E e t) ad
  .

(*

Inductive something : 
  | Something_Load
    tid = alguma thread
    m / ths ==> m' / ths' # Load tid 23
    em todas as outras threads que não são tid,
    não pode ter Loc 23
    
*)