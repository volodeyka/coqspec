From mathcomp Require Import ssreflect seq ssrnat eqtype ssrbool ssrfun.

Definition Atom  := nat.
Definition Name  := nat.
Definition FName := nat.

Inductive Val := ATOM of Atom.
Notation "'`' e" := (ATOM e) (at level 0).

Inductive Var := VAR of Name.

Inductive Arg := 
  | Arg_Val of Val
  | Arg_Var of Var.
Coercion Arg_Val : Val >-> Arg.
Coercion Arg_Var : Var >-> Arg.

Inductive Exp :=
  | Exp_Arg of Arg
  | CONS of Exp & Exp.
Coercion Exp_Arg : Arg >-> Exp.

Inductive Cntr :=
  | CONStest of Arg & Var & Var
  | ATOMtest of Arg & Arg.
Notation "'CONS?'" := (CONStest) (only parsing).
Notation "'EQA?'"  := (ATOMtest) (only parsing).

Inductive Tree := 
  | LET  of Var  & Exp  & Tree
  | COND of Cntr & Tree & Tree
  | EXP  of Exp.
Coercion EXP : Exp >-> Tree.

(*Inductive Def := DEFINE of FName & seq Var & Tree.*)

Inductive Const :=
  | Const_Val of Val
  | CCONS of Const & Const.
Coercion Const_Val : Val >-> Const.

Fixpoint ExpConst (e : Exp) : Const :=
  match e with
  | CONS e1 e2 => CCONS (ExpConst e1) (ExpConst e2)
  | `a         => `a
  | VAR a      => `a
  end.

Fixpoint ConstExp (c : Const) : Exp :=
  match c with
  | CCONS c1 c2 => CONS (ConstExp c1) (ConstExp c2)
  | `a          => `a 
  end.

Inductive Bind := BIND of Var & Const.
Notation "b ↦ c" := (BIND b c) (at level 100).

Definition Env := seq Bind.

Definition getExp (b : Bind) : Exp := 
  let: _ ↦ c := b in ConstExp c.

Definition ofind {T} a (s : seq T) := 
  ohead [seq x <- s | a x].

Fixpoint subst (e : Exp) (env : Env) : Exp := 
  match e with 
  | CONS e1 e2 => CONS (subst e1 env) (subst e2 env)
  | `a         => `a
  | VAR a      => oapp getExp e (ofind (fun '(VAR b ↦ _) => a == b) env)
  end.

Notation "e /. env" := (subst e env) (at level 100).