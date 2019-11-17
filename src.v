Require Import Coq.Init.Nat.

Definition nat_map: Type := nat -> nat.

Definition nat_map_empty: nat_map := (fun _ => 0).

Definition nat_map_update (m: nat_map) (key: nat) (value: nat) : nat_map :=
  fun k' => if k' =? key then value else m k'.

Notation "x '!->' v" := (nat_map_update nat_map_empty x v)
  (at level 100, v at next level, right associativity).

Notation "x '!->' v ';' m" := (nat_map_update m x v)
  (at level 100, v at next level, right associativity).

Inductive program : Type :=
  | p_single (f : function)
  | p_cons (f : function) (p : program)

with function : Type :=
  | f_func (fn : nat) (s : statement)

with statement : Type :=
  | s_skip
  | s_cons (i : instruction) (s : statement)

with instruction : Type :=
  | i_skip
  | i_assign (d : nat) (e : expression)
  | i_while (d : nat) (s : statement)
  | i_async (s : statement)
  | i_finish (s : statement)
  | i_call (f : function)

with expression : Type :=
  | e_const (c : nat)
  | e_add (d : nat).

Inductive contains : program -> nat -> Prop :=
  | c_single fn s : contains (p_single (f_func fn s)) fn
  | c_hd fn s p : contains (p_cons (f_func fn s) p) fn
  | c_tl p fn fn' s' : contains p fn -> contains (p_cons (f_func fn' s') p) fn.

Fixpoint find_function_body (p : program) (fn : nat) : statement :=
  match p with
  | p_single f => match f with
                | f_func fn' s => if fn =? fn' then s else s_skip
                end
  | p_cons f p' => match f with
                   | f_func fn' s => if fn =? fn' then s else find_function_body p' fn
                   end
  end.

Inductive well_formed : program -> Prop := .

Inductive tree : Type :=
  | t_ord (t1 : tree) (t2 : tree)
  | t_unord (t1 : tree) (t2 : tree)
  | t_stat (s : statement)
  | t_final.

Inductive array : Type :=.

Inductive steps_to : program -> array -> tree -> program -> array -> tree -> Prop := .

Theorem progress : forall (p : program) (a : array) (t : tree), well_formed p -> t = t_final \/ exists a' t', steps_to p a t p a' t'.