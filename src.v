Require Import Coq.Init.Nat.

(* ==================== program ==================== *)

Inductive statement : Type :=
  | s_skip                                   (* skip *)
  | s_cons (i : instruction) (s : statement) (* i s *)

with instruction : Type :=
  | i_skip                              (* skip *)
  | i_assign (d : nat) (e : expression) (* a[d] = e *)
  | i_while (d : nat) (s : statement)   (* while (a[d] /= 0) s *)
  | i_async (s : statement)             (* async s *)
  | i_finish (s : statement)            (* finish s *)
  | i_call (f : nat)                    (* f() *)

with expression : Type :=
  | e_const (c : nat) (* c *)
  | e_add (d : nat).  (* a[d] + 1 *)

Definition program := list statement.

Fixpoint concat (s1 : statement) (s2 : statement) : statement :=
  match s1 with
  | s_skip => s_cons i_skip s2               (* skip . s2 = skip s2 *)
  | s_cons i s1' => s_cons i (concat s1' s2) (* (i s1) . s2 = i (s1 . s2) *)
  end.

Fixpoint get_function_body (p : program) (n : nat) : statement :=
  match p with
  | nil => s_skip
  | cons s ss => if n =? 0 then s else get_function_body ss (n - 1)
  end.

(* ==================== array ==================== *)

Definition array : Type := nat -> nat.

Definition empty_array : array := (fun _ => 0).

Definition update_array (a : array) (key : nat) (value : nat) : array :=
  fun k' => if k' =? key then value else a k'.

Definition eval_expression (a : array) (e : expression) : nat :=
  match e with
  | e_const c => c       (* c *)
  | e_add d => (a d) + 1 (* a[d] + 1 *)
  end.

(* ==================== tree ==================== *)

Inductive tree : Type :=
  | t_ord (t1 : tree) (t2 : tree)   (* T |> T *)
  | t_unord (t1 : tree) (t2 : tree) (* T || T *)
  | t_stmt (s : statement)          (* <s> *)
  | t_finished.                     (* check mark *)

(* ==================== steps-to ==================== *)

Inductive steps_to : program -> array -> tree -> program -> array -> tree -> Prop :=
  | one p a t2 :
    steps_to p a (t_ord t_finished t2) p a t2
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

(* ==================== theorem ==================== *)

Theorem progress : forall (p : program) (a : array) (t : tree),
  t = t_finished \/ exists a' t', steps_to p a t p a' t'.
Proof.
  intros p a t.
  induction t; simpl.
  - right; destruct IHt1; subst.
    + exists a. exists t2. constructor.
    + inversion H. inversion H0.
      exists x. exists (t_ord x0 t2). constructor. assumption.
  - right; destruct IHt1; subst.
    + exists a. exists t2. constructor.
    + inversion H. inversion H0.
      exists x. exists (t_unord x0 t2). constructor. assumption.
  - right; destruct s.
    + exists a. exists t_finished. constructor.
    + destruct i.
      * exists a. exists (t_stmt s). constructor.
      * exists (update_array a d (eval_expression a e)).
        exists (t_stmt s). constructor.
      * assert (a d = 0 \/ a d <> 0).
        {
          destruct (a d).
          { left. reflexivity. }
          { right. discriminate. }
        }
        destruct H.
        { exists a. exists (t_stmt s). constructor. assumption. }
        {
          exists a.
          exists (t_stmt (concat s0 (s_cons (i_while d s0) s))).
          constructor. assumption.
        }
      * exists a. exists (t_unord (t_stmt s0) (t_stmt s)).
        constructor.
      * exists a. exists (t_ord (t_stmt s0) (t_stmt s)).
        constructor.
      * exists a. exists (t_stmt (concat (get_function_body p f) s)).
        constructor.
  - left. reflexivity.
Qed.