From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap choice finfun fintype.
From coqspec Require Import utilities substitution.
From deriving Require Import deriving.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.
Open Scope fset_scope.

Inductive Cntr :=
  | CONStest of Arg
  | ATOMtest of Exp & Exp.
Notation "CONS?" := (CONStest) (only parsing).
Notation "'EQA?'"  := (ATOMtest) (only parsing).

Definition FVCntr (c : Cntr) : {fset Var} := 
  match c with
  | EQA? x y => FVExp x `|` FVExp y
  | CONS? x  => FVArg x
  end.

Inductive Tree := 
  | RET  of Exp
  | LET  of Var  & Exp  & Tree
  | COND of Cntr & Tree & Tree
  | HT   of Var & Var & Var & Tree
  | CALL of FName & seq Exp.
Coercion RET : Exp >-> Tree.

Fixpoint VTree (t : Tree) : {fset Var} :=
  match t with
  | RET e        => FVExp e
  | LET v x t    => v |` (FVExp x `|` VTree t)
  | COND c t1 t2 => FVCntr c `|` VTree t1 `|` VTree t2
  | HT v u x t   => [fset v; u; x] `|`  (VTree t)
  | CALL f xs    => [fset x | y in xs, x in FVExp y]
  end.

Fixpoint FVTree (t : Tree) : {fset Var} :=
  match t with
  | RET e        => FVExp e
  | LET v x t    => (FVExp x `|` FVTree t) `\ v
  | COND c t1 t2 => FVCntr c `|` FVTree t1 `|` FVTree t2
  | HT v u x t   => (FVExp x `|` FVTree t) `\ v `\ u
  | CALL f xs    => [fset x | y in xs, x in FVExp y]
  end.

Definition maxvar (t : Tree) : Var := max_set (VTree t).

Lemma subst_max (e1 e2 : Env) (e : Exp) : 
  (forall x, x <= maxvar e -> e1 x = e2 x) ->
  e /s/ e1 = e /s/ e2.
Proof.
elim: e=> [[[]|?]|? IHe1 ? IHe2 I] //=; first apply.
- rewrite /maxvar /=; apply/max_setin; by rewrite ?inE.
  by rewrite IHe1 ?IHe2 //; move=> ? I'; apply/I; rewrite /maxvar /=;
rewrite max_setU leq_max I' ?orbT.
Qed.

Inductive Def := DEFINE of FName & seq Var & Tree.

Definition Prog := seq Def.

Inductive Branch := 
  | TRUE  of Env
  | FALSE of Env
  | ERR.

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

Fixpoint get_func (f : FName) (p : Prog) : (Tree * seq Var)%type := 
  match p with 
  | [::]                  => (RET ERROR, [::])
  | (DEFINE g xs t) :: ps => 
    if f == g then (t, xs)
    else get_func f ps
  end.

Fixpoint int (n : nat) (t : Tree) (e : Env) (p : Prog) : Exp := 
  match t with
  | RET x         => 
    if n is n'.+1 then 
      subst x e
    else ERROR
  | LET v x t     => 
    if n is n'.+1 then
      int n' t  [fsfun e with v |-> x /s/ e] p
    else ERROR
  | COND c t' t'' => 
    if n is n'.+1 then
      match cntr c e with
      | TRUE e'   => int n' t'  e'  p
      | FALSE e'' => int n' t'' e'' p
      | ERR       => ERROR
      end
    else ERROR
  | HT v u x t => 
    if n is n'.+1 then
      if x /s/ e is CONS a b then 
        int n' t [fsfun e with v |-> a, u |-> b] p
      else ERROR
    else ERROR
  | CALL f args => 
    if n is n'.+1 then
      let: (t, xs) := (get_func f p) in
        int n' t (mkEnv xs (map (subst^~ e) args)) p
    else ERROR
  end.

Lemma aux_CONS e a: 
  aux e (FVCntr (CONS? a)) = FVExp (a /s/ e).
Proof.
move=> /=; have->: FVArg a = FVExp a by case: a=> [[]|].
exact/aux_FVExp.
Qed.

Lemma aux_EQA e a1 a2: 
  aux e (FVCntr (EQA? a1 a2)) = FVExp (a1 /s/ e) `|` FVExp (a2 /s/ e).
Proof. by move=> /=; rewrite auxU ?aux_FVExp. Qed.

Lemma auxE e c rs: 
  aux e (FVCntr c) `<=` FVCntr c `|` whole (e, rs).
Proof.
apply/fsubsetP=> y /mem_aux[x I]. 
rewrite -[e x]/((Exp_Arg (Arg_Var x)) /s/ e)=> /(fsubsetP (whole_subst _ rs _)).
move=> /=; rewrite 2?inE => /orP[/eqP->|H]; first by rewrite inE I.
by rewrite inE H orbT.
Qed.

Lemma cntr_env_TRUE c env e: 
  cntr c env = TRUE e ->
  (env = e).
Proof.
case: c=> /= [?|??]; case: (_ /s/ env)=> //.
- by move=> ?? [].
by case=> // [[]] ?; case: (_ /s/ _)=> // [[]] // [] ?; case: ifP=> // ? [].
Qed.

Lemma cntr_env_FALSE c env e: 
  cntr c env = FALSE e -> e = env.
Proof. 
case: c=> [/= >|/= ??]; case (_ /s/ _)=> //; first by move=> ?[->].
case=> //[][]. case: (_ /s/ _)=> //[][]//[] ??.
by case:ifP=> // ?[->].
Qed.

Section IntSpec.

Context {p : Prog}.

Fixpoint well_typed (t : Tree) : bool := 
  match t with 
  | RET _ => true
  | LET v x t => well_typed t && (v \notin FVExp x)
  | COND c t1 t2 =>  well_typed t1 && well_typed t2 
  | HT v u x t => [&& x != v, x != u, v != u & well_typed t]
  | CALL f xs => size xs == size (get_func f p).2
  end.

Lemma int_freevar (e1 e2 : Env) t n: 
  well_typed t ->
  (forall x, x \in FVTree t -> e1 x = e2 x) ->
  int n t e1 p = int n t e2 p.
Proof.
elim: t e1 e2 n=> [??? n ? H *|??? IHt ?? n|c ? IHt1 ? IHt2 ++ n|?? v ? IHt e1 e2 n|++++ n].
all: case: n=> // n.
- apply/subst_fv=> *; exact/H.
- move=> /andP[? /negbTE NI I]; apply/IHt=> // ? F; rewrite ?fsfun_withE.
  case: ifP=> [/eqP E|N].
  - apply/subst_fv=> ? I'; apply/I; rewrite /= ?inE I' /= andbT.
    apply/negP=> /eqP E'; by rewrite E' NI in I'.
  by apply/I; rewrite ?inE F N orbT.
- case: c=> [[[a ?? /andP[??] I]|v e1 e2 /andP[??] I]|] /=.
  - apply/IHt2=> // ? I'; apply/I; by rewrite ?inE I' orbT.
  - have->: e1 v = e2 v by apply/I; rewrite ?inE eq_refl.
    case E: (e2 v); [apply/IHt2 | apply/IHt1] => // ? I'; apply/I;
    by rewrite ?inE I' orbT.
  - move=> e e' e1 e2 /andP[??] I.
    have->: (e /s/ e1 = e /s/ e2). 
    - by apply/subst_fv=> ? I'; apply/I; rewrite ?inE I'.
    case: (e /s/ e2)=> // [[[]|]] //= ?.
    have->: (e' /s/ e1 = e' /s/ e2).
    - by apply/subst_fv=> ? I'; apply/I; rewrite ?inE I' orbT.
    case: (e' /s/ e2)=> // [[]] // [?]; case: ifP=> ?;
    [apply/IHt1 | apply/IHt2] => // ? I'; apply/I; by rewrite ?inE I' ?orbT.
- case/and4P=> N1 N2 ?? I /=.
  have->: e1 v = e2 v.
  - by apply/I=> /=; rewrite ?inE N1 N2 eq_refl /=.
  case: (e2 v)=> // ??; apply/IHt=> // ? I'; rewrite ?fsfun_withE.
  (do? case: ifP=> //)=> N1' N2'; apply/I; by rewrite ?inE N1' N2' I' orbT.
move=> f l e1 e2 ? IH /=.
case: (get_func f p)=> ? xs.
have-> //: (mkEnv xs [seq x /s/ e1 | x <- l]) =  (mkEnv xs [seq x /s/ e2 | x <- l]).
apply/congr1/eq_in_map=> x H. apply/subst_fv=> y ?.
apply/IH/imfset2P; exists x=> //; by exists y.
Qed.

Lemma int_maxvar (e1 e2 : Env) t n: 
  well_typed t ->
  (forall x, x <= maxvar t -> e1 x = e2 x) ->
  int n t e1 p = int n t e2 p.
Proof.
move=> wf H; apply/int_freevar=> // ? I; rewrite H // /maxvar max_setin //.
elim: t I {wf H}=> //= [??? IH|?? IH1 ? IH2|???? IH]; rewrite ?inE.
- case/andP=> ? /orP[|/IH]->; by rewrite ?orbT.
- case/orP=> [/orP[|/IH1]|/IH2]->; by rewrite ?orbT.
case/and3P=> ?? /orP[|/IH]->; by rewrite ?orbT.
Qed.

Arguments int: simpl nomatch.

Lemma int_not0 n t e: 
  int n t e p <> ERROR ->
  int n t e p = int n.+1 t e p.
Proof.
elim: n t e p=> [[]|] // n IH [] //=.
- move=> *; by rewrite IH.
- move=> c ?? e ?; case: c=> //= [[[]??|v]|] //=; rewrite 1?IH //;
  rewrite /int /= -/int.
  - case E: (e v)=> ?; by rewrite IH.
  move=> e1 e2 /=. case: (e1 /s/ e)=> //= [[]] // [] //.
  case (e2 /s/ e)=> [] // [] // [] ??; case: ifP=> ??; by rewrite IH.
- move=> ?? v ?; rewrite /int/= -/int=> e; case: (e v)=> // *.
  by rewrite IH.
move=> ????. rewrite {1 2 3}/int/=-/int. case: (get_func _ _)=> // ???.
by rewrite IH.
Qed.

End IntSpec.








