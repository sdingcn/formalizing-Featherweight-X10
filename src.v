Require Import Coq.Init.Nat.

(* ==================== program ==================== *)

Inductive statement : Type :=
  | s_skip
  | s_cons (i : instruction) (s : statement)

with instruction : Type :=
  | i_skip
  | i_assign (d : nat) (e : expression)
  | i_while (d : nat) (s : statement)
  | i_async (s : statement)
  | i_finish (s : statement)
  | i_call (f : nat)

with expression : Type :=
  | e_const (c : nat)
  | e_add (d : nat).

Definition program := list statement.

Fixpoint concat (s1 : statement) (s2 : statement) : statement :=
  match s1 with
  | s_skip => s_cons i_skip s2
  | s_cons i s => s_cons i (concat s s2)
  end.

Fixpoint well_formed_statement (s : statement) (n : nat) : Prop :=
  match s with
  | s_skip => True
  | s_cons i s' => match i with
                  | i_skip => well_formed_statement s' n
                  | i_assign d e => well_formed_statement s' n
                  | i_while d s'' => well_formed_statement s'' n /\ well_formed_statement s' n
                  | i_async s'' => well_formed_statement s'' n /\ well_formed_statement s' n
                  | i_finish s'' => well_formed_statement s'' n /\ well_formed_statement s' n
                  | i_call fi => fi < n /\ well_formed_statement s' n
                  end
  end.

Fixpoint well_formed_program (p : program) (n : nat) : Prop :=
  match p with
  | nil => True
  | cons s tl => well_formed_statement s n /\ well_formed_program tl n
  end.

Fixpoint get_function_body (p : program) (n : nat) : statement :=
  match p with
  | nil => s_skip
  | cons s tl => if n =? 0 then s else get_function_body tl (n - 1)
  end.

(* ==================== array ==================== *)

Definition array : Type := nat -> nat.

Definition empty_array : array := (fun _ => 0).

Definition update_array (a : array) (key : nat) (value : nat) : array :=
  fun k' => if k' =? key then value else a k'.

Notation "x '!->' v" := (update_array empty_array x v)
  (at level 100, v at next level, right associativity).

Notation "x '!->' v ';' a" := (update_array a x v)
  (at level 100, v at next level, right associativity).

Definition eval_expression (a : array) (e : expression) : nat :=
  match e with
  | e_const c => c
  | e_add d => (a d) + 1
  end.

(* ==================== tree ==================== *)

Inductive tree : Type :=
  | t_ord (t1 : tree) (t2 : tree)
  | t_unord (t1 : tree) (t2 : tree)
  | t_stmt (s : statement)
  | t_finished.

Fixpoint well_formed_tree (t : tree) (n : nat) : Prop :=
  match t with
  | t_ord t1 t2 => well_formed_tree t1 n /\ well_formed_tree t2 n
  | t_unord t1 t2 => well_formed_tree t1 n /\ well_formed_tree t2 n
  | t_stmt s => well_formed_statement s n
  | t_finished => True
  end.

(* ==================== steps-to ==================== *)

Inductive steps_to : program -> array -> tree -> program -> array -> tree -> Prop :=
  | one p a t :
    steps_to p a (t_ord t_finished t) p a t
  | two p a t1 a' t1' t2 :
    steps_to p a t1 p a' t1' ->
    steps_to p a (t_ord t1 t2) p a' (t_ord t1' t2)
  | three p a t2 :
    steps_to p a (t_unord t_finished t2) p a t2
  | four p a t1 :
    steps_to p a (t_unord t1 t_finished) p a t1
  | five p a t1 a' t1' t2 :
    steps_to p a t1 p a' t1' ->
    steps_to p a (t_unord t1 t2) p a' (t_unord t1' t2)
  | six p a t2 a' t2' t1 :
    steps_to p a t2 p a' t2' ->
    steps_to p a (t_unord t1 t2) p a' (t_unord t1 t2')
  | seven p a :
    steps_to p a (t_stmt s_skip) p a t_finished
  | eight p a k :
    steps_to p a (t_stmt (s_cons i_skip k)) p a (t_stmt k)
  | nine p a d e k :
    steps_to p a (t_stmt (s_cons (i_assign d e) k)) p (update_array a d (eval_expression a e)) (t_stmt k)
  | ten a d p s k :
    a d = 0 ->
    steps_to p a (t_stmt (s_cons (i_while d s) k)) p a (t_stmt k)
  | eleven a d p k s :
    a d <> 0 ->
    steps_to p a (t_stmt (s_cons (i_while d s) k)) p a (t_stmt (concat s (s_cons (i_while d s) k)))
  | twelve p a s k :
    steps_to p a (t_stmt (s_cons (i_async s) k)) p a (t_unord (t_stmt s) (t_stmt k))
  | thirteen p a s k :
    steps_to p a (t_stmt (s_cons (i_finish s) k)) p a (t_ord (t_stmt s) (t_stmt k))
  | fourteen p a f k :
    steps_to p a (t_stmt (s_cons (i_call f) k)) p a (t_stmt (concat (get_function_body p f) k)).

Theorem progress : forall (p : program) (a : array) (t : tree),
  well_formed_program p (length p) ->
  well_formed_tree t (length p) ->
  t = t_finished \/ exists a' t', steps_to p a t p a' t'.
Proof.
  intros p a t H1 H2.
  induction t; simpl.
  - destruct IHt1.
    + simpl in H2. apply H2.
    + right. exists a. exists t2. subst. apply one.
    + right. inversion H. inversion H0. exists x. exists (t_ord x0 t2). constructor. assumption.
  - destruct IHt1.
    + simpl in H2. apply H2.
    + right. exists a. exists t2. subst. constructor.
    + right. inversion H. inversion H0. exists x. exists (t_unord x0 t2). constructor. assumption.
  - destruct s.
    + right. exists a. exists t_finished. constructor.
    + destruct i; right.
      * exists a. exists (t_stmt s). constructor.
      * exists (update_array a d (eval_expression a e)). exists (t_stmt s). constructor.
      * exists a. assert (a d = 0 \/ a d <> 0). { destruct (a d). { left. reflexivity. } { right. discriminate. } }
        destruct H.
        { exists (t_stmt s). apply ten. apply H. }
        { exists (t_stmt (concat s0 (s_cons (i_while d s0) s))). apply eleven. apply H. }
      * exists a. exists (t_unord (t_stmt s0) (t_stmt s)). constructor.
      * exists a. exists (t_ord (t_stmt s0) (t_stmt s)). constructor.
      * exists a. exists (t_stmt (concat (get_function_body p f) s)). constructor.
  - left. reflexivity.
Qed.