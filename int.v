From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap choice finfun fintype.
From deriving Require Import deriving.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.
Open Scope fset_scope.
Definition Atom  := nat.
Definition Var  := nat.
Definition FName := nat.

Inductive Val := ATOM of Atom.
Notation "''' e" := (ATOM e) (at level 0).

Definition val_indDef := [indDef for Val_rect].
Canonical val_indType := IndType Val val_indDef.

Definition val_eqMixin := [derive eqMixin for Val].
Canonical val_eqType := EqType Val val_eqMixin.
Definition val_choiceMixin := [derive choiceMixin for Val].
Canonical val_choiceType := Eval hnf in ChoiceType Val val_choiceMixin.

Inductive Arg := 
  | Arg_Val of Val
  | Arg_Var of Var.
Coercion Arg_Val : Val >-> Arg.
Coercion Arg_Var : Var >-> Arg.

Definition arg_indDef := [indDef for Arg_rect].
Canonical arg_indType := IndType Arg arg_indDef.

Definition eq_arg a b := 
  match a, b with
  | Arg_Val 'a, Arg_Val 'b => a == b
  | Arg_Var x, Arg_Var y => x == y
  | _, _ => false
  end.

Lemma eqargP : Equality.axiom eq_arg.
Proof. 
by case=> [[]?[[]|]|?[]]?/=; try (by constructor); apply/(iffP eqP)=> [|[]]->. 
Qed.

Canonical arg_eqMixin := EqMixin eqargP.
Canonical arg_eqType := Eval hnf in EqType Arg arg_eqMixin.

Definition arg_choiceMixin := [derive choiceMixin for Arg].
Canonical arg_choiceType := Eval hnf in ChoiceType Arg arg_choiceMixin.

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

Definition exp_indDef := [indDef for Exp_rect].
Canonical exp_indType := IndType Exp exp_indDef.

Definition exp_choiceMixin := [derive choiceMixin for Exp].
Canonical exp_choiceType := Eval hnf in ChoiceType Exp exp_choiceMixin.

Inductive Cntr :=
  | CONStest of Arg
  | ATOMtest of Exp & Exp.
Notation "CONS?" := (CONStest) (only parsing).
Notation "'EQA?'"  := (ATOMtest) (only parsing).

Inductive Tree := 
  | RET  of Exp
  | LET  of Var  & Exp  & Tree
  | COND of Cntr & Tree & Tree
  | HT   of Var & Var & Var & Tree
  | CALL of FName & seq Var.
Coercion RET : Exp >-> Tree.

Inductive Prog := DEFINE of FName & seq Var & Tree.

Definition Programm := seq Prog.

Definition Env := {fsfun Var -> Exp for id}.

(*Definition getExp (b : Bind) : Exp := 
  let: _ ↦ c := b in c.

Definition ofind {T} a (s : seq T) := 
  ohead [seq x <- s | a x].*)

Fixpoint subst (e : Exp) (env : Env) : Exp := 
  match e with 
  | CONS e1 e2 => CONS (subst e1 env) (subst e2 env)
  | 'a         => 'a
  | (Exp_Arg (Arg_Var v))      =>  env v 
  end.

Notation "e '/s/' env" := (subst e env) (at level 1, left associativity).

Arguments subst : simpl nomatch.

Inductive Branch := 
  | TRUE  of Env
  | FALSE of Env
  | ERR.

Definition csub (e1 : Env) (e2 : Env) : Env := 
  [fsfun x in finsupp e1 => subst (e1 x) e2].

Definition comp (e1 e2 : Env) : Env := 
  [fsfun x in (finsupp e1 `|` finsupp e2) => (e1 x) /s/ e2].

Definition emsub : Env := [fsfun for (id : Var -> Exp)].


Definition cntr (c : Cntr) (e : Env) : Branch := 
  match c with
  | EQA? x y    => 
    match x /s/ e, y /s/ e with
    | Arg_Val 'a, Arg_Val 'b => if a == b then TRUE e else FALSE e
    | _, _ => ERR
    end
  | CONS? x =>
    if x /s/ e is CONS a _ then
      TRUE e
    else FALSE e
  end.

Fixpoint get_func (f : FName) (p : Programm) : (Tree * seq Var)%type := 
  match p with 
  | [::]                  => (RET '0, [::])
  | (DEFINE g xs t) :: ps => 
    if f == g then (t, xs)
    else get_func f ps
  end.

Definition fmap_of (ks : seq Var) (vs : seq Exp) : Env :=
  foldr comp emsub (map (fun '(a, b)=> [fsfun emsub with a |-> b]) (zip ks vs)).

Definition State := (Tree * Env)%type.

Fixpoint int (t : Tree) (e : Env) (p : Programm) : State := 
  match t with
  | RET x         => (RET (subst x e), emsub)
  | LET v x t     => 
    int t  [fsfun e with v |-> x /s/ e] p
  | COND c t' t'' => 
    match cntr c e with
    | TRUE e'   => int t'  e'  p
    | FALSE e'' => int t'' e'' p
    | ERR       => (RET '0, emsub)
    end
  | HT v u x t => 
    if x /s/ e is CONS a b then 
      int t [fsfun e with v |-> a, u |-> b] p
    else (RET '0, emsub)
  | CALL f args => 
    let: (t, xs) := (get_func f p) in
      (t, fmap_of xs (map e args))
  end.

Definition int_to_step (s1 s2 : State) (p : Programm) := 
  let: (t, e) := s1 in
  int t e p = s2.

Inductive int_to := .


Definition int_Prog (f : Prog) (e : seq Exp) := 
  let: DEFINE _ vs t := f in
  int t (fmap_of vs e).

Lemma l (K V : choiceType) (k : K) (v x : V) (f : {fmap K -> V}) : 
  x \in codomf f.[k <- v] -> (x \in codomf f) || (v == x).
Proof. 
  rewrite ?inE=> /existsP[[y I /eqP H]] . 
  move/eqP: (congr1 Some H); rewrite Some_fnd fnd_set /=.
  move: I {H}; rewrite ?inE; case: ifP=> /= [?? /eqP[->]| ? L].
  - by rewrite eq_refl orbT.
  rewrite -[y]/(val [`L]) -Some_fnd=> /eqP[/eqP?].
  by apply/orP; left; apply/existsP; exists [`L].
Qed.

Lemma domf_fmap_of (ks : seq Var) (vs : seq Exp) x:
   size vs = size ks ->
   x \in finsupp (fmap_of ks vs) = (x \in ks).
Proof. Admitted.

Lemma codomf_fmap_of (ks : seq Var) (vs : seq Exp) x:
   x \in finsupp (fmap_of ks vs) -> (fmap_of ks vs x) \in vs.
Proof. Admitted.

Fixpoint FVExp (e : Exp) : {fset Var} := 
  match e with
  | CONS e1 e2 => FVExp e1 `|` FVExp e2
  | (Exp_Arg (Arg_Var v))      => [fset v]
  | _          => fset0
  end.

Definition closed e := FVExp e == fset0.

Definition FVArg (a : Arg) := 
  if a is (Arg_Var x) then [fset x] else fset0.

Definition FVCntr (c : Cntr) : {fset Var} := 
  match c with
  | EQA? x y => FVExp x `|` FVExp y
  | CONS? x  => FVArg x
  end.

Fixpoint FVTree (t : Tree) : {fset Var} :=
  match t with
  | RET e        => FVExp e
  | LET v x t    => (FVExp x `|` FVTree t) `\ v
  | COND c t1 t2 => FVCntr c `|` FVTree t1 `|` FVTree t2
  | HT v u x t     => (FVExp x `|` FVTree t) `\ v `\ u
  end.

Definition closed_sub (e : Env) := 
  forall x, x \in finsupp e -> closed (e x).


Lemma closed_subs e (env : Env): 
  FVExp e `<=` finsupp env -> 
  (closed_sub env) -> closed e /s/ env.
Proof.
(*elim: e=> [[[]|[]]|]//=.
- move=> n; rewrite fsub1set /subst=>L. 
  rewrite -[VAR n]/(val [` L]) -Some_fnd /=; apply; by rewrite in_codomf.
rewrite /closed; move=> ? IHe1 ? IHe2 /fsubUsetP[] *.
by rewrite /closed/= fsetU_eq0 IHe1 // IHe2.
Qed.*)
Admitted.

Lemma cntr_env_TRUE c env e: 
  cntr c env = TRUE e ->
  (env = e).
Proof.
case: c=> /= [?|??]; case: (_ /s/ env)=> //.
- by move=> ?? [].
by case=> // [[]] ?; case: (_ /s/ _)=> // [[]] // [] ?; case: ifP=> // ? [].
Qed.
(*case: c=> [/= a v u |/= ??].
- case: a; rewrite /subst=> [[]]; first move=> []//.
  move=> n; case: (boolP (VAR n \in domf env))=>[L|/not_fnd->//].
  rewrite -[VAR n]/(val [` L]) -Some_fnd /=.
  case E: (env.[_])=> // [][] <- H.
  have: closed (env.[L]); first (by apply/H; rewrite ?in_codomf).
  rewrite E /= /closed /= fsetU_eq0=> /andP[??].
  rewrite ?dom_setf (fsubset_trans (fsubsetU1 _ _) (fsubsetU1 _ _)).
  by split=> // ? /l /orP[/l/orP[/H|/eqP<-]|/eqP<-].
case: (_ /s/ _) => // [[[]|]|?]; try by move=> ?[->].
- case: (_ /s/ _)=> //[[[]|??[->]]|???[->]]// ??.
by case: ifP=> // ? [->].
Qed.*)

Lemma cntr_env_FALSE c env e: 
  cntr c env = FALSE e -> e = env.
Proof. 
case: c=> [/= >|/= ??]; case (_ /s/ _)=> //; first by move=> ?[->].
case=> //[][]. case: (_ /s/ _)=> //[][]//[] ??.
by case:ifP=> // ?[->].
Qed.

Lemma closed_int t e: 
  FVTree t `<=` finsupp e -> 
  closed_sub e ->
  closed (int t e).
Proof.
(*elim: t e => [|v > IHt ? /= /fsubsetP H C|] //=.
- elim=> [[[]//|[]/= n ?]|/=]. 
  rewrite fsub1set=> L; rewrite -[VAR n]/(val [` L]) -Some_fnd /=.
  apply; by rewrite in_codomf.
- rewrite /closed => ? IHt1 ? IHt2 ? /fsubUsetP[]*. 
  by rewrite fsetU_eq0 IHt1 // IHt2.
- rewrite IHt // ?dom_setf.
  - apply/fsubsetP=> ?; rewrite ?inE; case: (boolP (_ == v))=> //= N I.
    by apply/H; rewrite ?inE N I /= orbT.
  move=> ? /l /orP[/C//|/eqP<-]; apply/closed_subs; rewrite ?dom_setf.
  - apply/fsubsetP=> ?; rewrite ?inE; case: (boolP (_ == v))=> //= N I.
    by apply/H; rewrite ?inE N I.
  by move=> ? /l=> /orP[/C|/eqP<-].
move=> c ? IHt ? IHt1 e; case E: (cntr c e); move: E=> //.
- move/cntr_env_TRUE=> H /fsubUsetP[/fsubUsetP[???]] /H[? sub] //.
  - apply/IHt=> //. exact/(fsubset_trans _ sub).
move/cntr_env_FALSE/eqP-> => /fsubUsetP[??] *; exact/IHt1.
Qed.*) Admitted.

Theorem closed_int_Prog t vs f e: 
  all closed e -> size e = size vs ->
  {subset FVTree t <= vs} ->
  closed (int_Prog (DEFINE f vs t) e).
Proof.
move=> /= /allP I ? S; apply/closed_int=> [|? /codomf_fmap_of /I]//.
apply/fsubsetP=> ? /S; by rewrite domf_fmap_of. 
Qed.







