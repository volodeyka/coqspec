From mathcomp Require Import ssreflect  ssrnat eqtype ssrbool ssrfun seq.
From coqspec Require Import int.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Inductive Restr := Neq of Exp & Exp.

Notation "e1 '≠' e2" := (Neq e1 e2) (at level 10).

Definition Cenv := (Env * seq Restr)%type.

Definition contr (r : Restr) := 
  match r with
  | (Arg_Var v) ≠ (Arg_Var u)   => v == u
  | (Arg_Val 'v) ≠ (Arg_Val 'u) => v == u
  | (CONS _ _) ≠   (CONS _ _)   => true
  | _                           => false
  end.


Definition contradict (c : Cenv) : bool :=
  has contr c.2.

Definition extend (c : Cenv) (b : Env) := 
  let: (e, r) := c in (b ++ e, r).

Definition rsubst (r : seq Restr) (e : Env) : seq Restr := 
  map (fun '(r1 ≠ r2) => r1 /s/ e ≠ r2 /s/ e) r.

Definition b2r : Bind -> Restr := fun '(a ↦ b) => a ≠ b.

Definition csubst (c : Cenv) (e : Env) := 
  let: (ce, r) := c in
  (map (fun '(v ↦ x) => v ↦ (subst x e)) ce, rsubst r e).

Definition restr (c : Cenv) (b : Bind) := 
  let: (e, r) := c in
  (e, b2r b :: r).

Inductive CBranch := 
  | CTRUE  of Cenv
  | CFALSE of Cenv
  | CBOTH  of Cntr & Cenv & Cenv.

Definition both (c : Cntr) (te fe : Cenv) (b : Bind) :=
  let: e1 := csubst te [:: b] in
  let: e2 := restr  fe b in
  if contradict e1 then
    CFALSE e2
  else CBOTH c e1 e2.

Definition dev_cntr (c : Cntr) (ce : Cenv) : CBranch :=
  match c with
  | EQA? x y => 
    let: x' := x /s/ (ce.1) in
    let: y' := y /s/ (ce.1) in
    match x', y' with
    | Arg_Val 'a, Arg_Val 'b
    | Arg_Var a,  Arg_Var b  => if a == b then CTRUE ce else CFALSE ce
    | Arg_Var v, Arg_Val u   => 
      both (EQA? (Arg_Var v) (Arg_Val u)) ce ce (v ↦ y')
    | Arg_Val u, Arg_Var v   => 
      both (EQA? (Arg_Val u) (Arg_Var v)) ce ce (v ↦ y')
    | _, _ => CFALSE ce 
    end
  | CONS? x h t =>
    let: x' := x /s/ (ce.1) in
    match x' with
    | CONS a b  => CTRUE (extend ce ((h ↦ a) :: [:: t ↦ b]))
    | Arg_Val _ => CFALSE ce
    | Arg_Var v => both (CONS? v h t) ce ce (v ↦ CONS h t)
    end
  end.

Fixpoint dev (t : Tree) (e : Cenv) : Tree :=
  match t with
  | RET x        => x /s/ (e.1)
  | LET v x t    => dev t (extend e [:: v ↦ x /s/ (e.1)])
  | COND c t1 t2 => 
    match dev_cntr c e with
    | CTRUE e       => dev t1 e
    | CFALSE e      => dev t2 e
    | CBOTH c e1 e2 => COND c (dev t1 e1) (dev t2 e2)
    end
  end.

Definition dev_Prog (f : Prog) (e : seq Exp) := 
  let: DEFINE n vs t := f in
  let: s := size e in
  DEFINE n (drop s vs) (dev t (zip vs e, [::])).

Theorem int_dev (p : Prog) (e1 e2 : seq Exp): 
  let: DEFINE n vs t := p in
  size e1 + size e2 = size vs ->
  int_Prog p (e1 ++ e2) = int_Prog (dev_Prog p e1) e2.
Proof. Admitted.
