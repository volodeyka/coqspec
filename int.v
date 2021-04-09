From mathcomp Require Import ssreflect  ssrnat eqtype ssrbool ssrfun seq.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Definition Atom  := nat.
Definition Name  := nat.
Definition FName := nat.

Inductive Val := ATOM of Atom.
Notation "''' e" := (ATOM e) (at level 0).

Inductive Var := VAR of Name.

Definition eq_var  :=
  fun '(VAR x) '(VAR y) => x == y.

Lemma eqvarP : Equality.axiom eq_var.
Proof. by case=> ?[?/=]; apply/(iffP eqP)=> [|[]]->. Qed.

Canonical var_eqMixin := EqMixin eqvarP.
Canonical var_eqType := Eval hnf in EqType Var var_eqMixin.

Inductive Arg := 
  | Arg_Val of Val
  | Arg_Var of Var.
Coercion Arg_Val : Val >-> Arg.
Coercion Arg_Var : Var >-> Arg.

Definition eq_arg a b := 
  match a, b with
  | Arg_Val 'a, Arg_Val 'b => a == b
  | Arg_Var (VAR x), Arg_Var (VAR y) => x == y
  | _, _ => false
  end.

Lemma eqargP : Equality.axiom eq_arg.
Proof. 
  by case=> [][]?[][]?/=; try (by constructor); apply/(iffP eqP)=> [|[]]->. 
Qed.

Canonical arg_eqMixin := EqMixin eqargP.
Canonical arg_eqType := Eval hnf in EqType Arg arg_eqMixin.

Inductive Exp :=
  | Exp_Arg of Arg
  | CONS of Exp & Exp.
Coercion Exp_Arg : Arg >-> Exp.

Fixpoint eq_exp a b := 
  match a, b with
  | Exp_Arg a,  Exp_Arg b  => a == b
  | CONS e1 e2, CONS e3 e4 => eq_exp e1 e3 && eq_exp e2 e4
  | _,          _          => false
  end.

Lemma eqexpP : Equality.axiom eq_exp.
Proof.
elim=> [?[]*|? IHe1 ? IHe2[]]/= *; first by apply/(iffP eqP)=> [|[]]//->.
1,2: by constructor.
by apply/(iffP andP)=> [][]/IHe1->/IHe2->.
Qed.

Canonical exp_eqMixin := EqMixin eqexpP.
Canonical exp_eqType := Eval hnf in EqType Exp exp_eqMixin.

Inductive Cntr :=
  | CONStest of Arg & Var & Var
  | ATOMtest of Arg & Arg.
Notation "'CONS?'" := (CONStest) (only parsing).
Notation "'EQA?'"  := (ATOMtest) (only parsing).

Inductive Tree := 
  | RET  of Exp
  | LET  of Var  & Exp  & Tree
  | COND of Cntr & Tree & Tree.
Coercion RET : Exp >-> Tree.

Inductive Prog := DEFINE of FName & seq Var & Tree.

Definition Bind := (Var * Exp)%type.
Notation "b ↦ c" := (b, c) (at level 100).

Definition Env := seq Bind.

Definition getExp (b : Bind) : Exp := 
  let: _ ↦ c := b in c.

Definition ofind {T} a (s : seq T) := 
  ohead [seq x <- s | a x].

Fixpoint subst (e : Exp) (env : Env) : Exp := 
  match e with 
  | CONS e1 e2 => CONS (subst e1 env) (subst e2 env)
  | 'a         => 'a
  | VAR a      => head e [seq x.2 | x <- env & x.1 == VAR a]
  end.

Notation "e '/s/' env" := (subst e env) (at level 0).

Arguments subst : simpl never.

Inductive Branch := 
  | TRUE  of Env
  | FALSE of Env.

Definition cntr (c : Cntr) (e : Env) : Branch := 
  match c with
  | EQA? x y    => 
    match x /s/ e, y /s/ e with
    | Arg_Val 'a, Arg_Val 'b => if a == b then TRUE e else FALSE e
    | _,   _ => FALSE e
    end
  | CONS? x h t => 
    if x /s/ e is CONS a b then
      TRUE ((h ↦ a) :: (t ↦ b) :: e)
    else FALSE e
  end.


Fixpoint int (t : Tree) (e : Env) : Exp := 
  match t with
  | RET x         => subst x e
  | LET v x t     => int t ((v ↦ x /s/ e) :: e)
  | COND c t' t'' => 
    match cntr c e with
    | TRUE e'   => int t'  e'
    | FALSE e'' => int t'' e''
    end
  end.

Definition int_Prog (f : Prog) (e : seq Exp) := 
  let: DEFINE _ vs t := f in
  int t (zip vs e).

Fixpoint FVExp (e : Exp) : seq Var := 
  match e with
  | CONS e1 e2 => FVExp e1 ++ FVExp e2
  | VAR v      => [:: VAR v]
  | _          => [::]
  end.

Definition closed e := FVExp e == [::].


Definition FVArg (a : Arg) := 
  if a is (Arg_Var x) then [:: x] else [::].


Definition FVCntr (c : Cntr) : seq Var := 
  match c with
  | EQA? x y => FVArg x ++ FVArg y
  | CONS? x h t => h :: t :: FVArg x
  end.

Fixpoint FVTree (t : Tree) : seq Var :=
  match t with
  | RET e        => FVExp e
  | LET v x t    => FVExp x ++ [seq fv <- FVTree t | fv != v ]
  | COND c t1 t2 => FVCntr c ++ FVTree t1 ++ FVTree t2
  end.

Lemma closed_subs e env: 
  {subset FVExp e <= [seq i.1 | i <- env]} -> 
  all closed [seq x.2 | x <- env] -> closed e /s/ env.
Proof.
elim: e=> [[[]|[]]|]//=.
- rewrite /subst=> n H /allP; apply.
  elim: env H=> //= [/(_ (VAR n))|[]/=]; first (apply; by rewrite inE).
  move=> ???; case: ifP=> //=; first by rewrite inE eq_refl.
  rewrite inE => E  H S; rewrite H ?orbT // => ? /[dup] /S /[swap].
  rewrite inE=> /eqP->; by rewrite inE eq_sym E.
move=> ? IHe1 ? IHe2 S?.
rewrite /subst/closed/= -size_eq0 size_cat addn_eq0 ?size_eq0 -/subst.
apply/andP; split.
- apply/IHe1=>// ? I; apply/S; by rewrite mem_cat I.
- apply/IHe2=>// ? I; apply/S; by rewrite mem_cat I orbT.
Qed.

Lemma cntr_env_TRUE c env e: 
  cntr c env = TRUE e -> all closed [seq x.2 | x <- env] -> 
  all closed [seq x.2 | x <- e] * subseq env e.
Proof.
case: c=> [/= a v u |/=??].
- case: a; rewrite /subst=> [[]]; first move=> []//.
  move=> n; case E : ([seq x.2 | x <- env & x.1 == VAR n])=> [|h l] //=.
  move: E=> /[swap]; case: h=> // a b [<-].
  rewrite (subseq_trans (subseq_cons env (u ↦ b))) ?subseq_cons //= => E.
  move=> /[dup] A; move: (mem_head (CONS a b) l); rewrite -E=> /mapP[[/= ??]].
  rewrite mem_filter/= => /andP[? /[swap]<-] /(map_f snd) H /allP/(_ _ H).
  move=> /=; rewrite A /closed/= -size_eq0 size_cat addn_eq0 ?size_eq0.
  by case/andP=>->->.
case: (_ /s/ _)=> // [[]]// []?; case: (_ /s/ _)=> // [[]] // []?.
case: ifP=> // ? [->]->; by rewrite subseq_refl.
Qed.

Lemma cntr_env_FALSE c env e: 
  cntr c env = FALSE e -> e == env.
Proof.
case: c=> [/= >|/= ??]; case (_ /s/ _)=> //; first by move=> ?[->].
2: by move=> ?? [->].
case=> [[]|?[->]]//; case: (_ /s/ _)=> [[[]??|??[->]]|???[->]]//.
by case:ifP=> // ?[->].
Qed.

Lemma closed_int t e: 
  {subset FVTree t <= map fst e} -> all closed (map snd e) ->
  closed (int t e).
Proof.
elim: t e => [|v > IHt ? H C|] /=.
- elim=> [[[]//|[]/= n e S /allP H]|/=]; first apply/H.
  elim: e S {H}=> [/(_ (VAR n)) |]; first by apply; rewrite inE.
  move=> []/= ???; rewrite/subst=> /=.
  case: ifP=> /=; first by rewrite inE eq_refl.
  rewrite inE => E  H S; rewrite H ?orbT // => ? /[dup] /S /[swap].
  rewrite inE=> /eqP->; by rewrite inE eq_sym E.
- rewrite /closed => ? IHt1 ? IHt2 ? S ?. 
  rewrite /= -size_eq0 size_cat addn_eq0 ?size_eq0.
  rewrite IHt1 /= ?IHt2 //= => ? I; apply S; by rewrite mem_cat I ?orbT.
- rewrite IHt /= ?C ?andbT => //= => [x|].
  - case: (boolP (x == v))=> [/eqP->|E I]; rewrite inE ?eq_refl //.
    apply/orP; right; apply/H; by rewrite mem_cat mem_filter E I /= orbT.
  apply/closed_subs=> //; rewrite /closed=> ? I; apply/H; by rewrite mem_cat I.
move=> c ? IHt ? IHt1 e; case E: (cntr c e); move: E.
- move/cntr_env_TRUE=> H S /H[? sub]; apply/IHt=> // x I.
  apply/(mem_subseq (map_subseq _ sub))/S; by rewrite ?mem_cat I /= orbT.
move/cntr_env_FALSE/eqP-> => S *; apply/IHt1=> // ? I; apply/S.
by rewrite ?mem_cat I /= ?orbT.
Qed.

Theorem closed_int_Prog t vs f e: 
  all closed e -> size vs = size e ->
  {subset FVTree t <= vs} ->
  closed (int_Prog (DEFINE f vs t) e).
Proof.
move=> /= ? E S; apply/closed_int=> [?|].
- rewrite -/unzip1 unzip1_zip ?E ?leqnn=> [/S|] //.
by rewrite -/unzip2 unzip2_zip ?E ?leqnn.
Qed.







