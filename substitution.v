From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap choice finfun fintype.
From deriving Require Import deriving.
From coqspec Require Import utilities.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.
Open Scope fset_scope.
Definition Atom  := nat.
Definition Var  := nat.
Definition FName := nat.

Inductive Val := ATOM of Atom.
Notation "''' e" := (ATOM e) (at level 0).

Notation "'ERROR'" := ('0) (only parsing).

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

Definition Env := {fsfun Var -> Exp for id}.

Fixpoint subst (e : Exp) (env : Env) : Exp := 
  match e with 
  | CONS e1 e2 => CONS (subst e1 env) (subst e2 env)
  | 'a         => 'a
  | (Exp_Arg (Arg_Var v))      =>  env v 
  end.

Notation "e '/s/' env" := (subst e env) (at level 1, left associativity).

Arguments subst : simpl nomatch.

Definition comp (e1 e2 : Env) : Env := 
  [fsfun x in (finsupp e1 `|` finsupp e2) => (e1 x) /s/ e2].

Definition emsub : Env := [fsfun for (id : Var -> Exp)].

Definition mkEnv (ks : seq Var) (vs : seq Exp) : Env :=
  foldr (fun '(v, x) a => [fsfun a with v |-> x]) emsub (zip ks vs).

Fixpoint FVExp (e : Exp) : {fset Var} := 
  match e with
  | CONS e1 e2 => FVExp e1 `|` FVExp e2
  | (Exp_Arg (Arg_Var v))      => [fset v]
  | _          => fset0
  end.

Definition closed e := FVExp e == fset0.

Definition FVArg (a : Arg) := 
  if a is (Arg_Var x) then [fset x] else fset0.

Definition closed_sub (e : Env) := 
  forall x, x \in finsupp e -> closed (e x).

Inductive Restr := 
  | Neq of Arg & Arg
  | NCONS of Arg.

Definition restr_indDef := [indDef for Restr_rect].
Canonical restr_indType := IndType Restr restr_indDef.

Definition restr_eqMixin := [derive eqMixin for Restr].
Canonical restr_eqType := Eval hnf in EqType Restr restr_eqMixin.

Definition restr_choiceMixin := [derive choiceMixin for Restr].
Canonical restr_choiceType := Eval hnf in ChoiceType Restr restr_choiceMixin.

Notation "e1 '≠' e2" := (Neq e1 e2) (at level 10).

Definition Cenv := (Env * seq Restr)%type.

Definition FVRestr (r : Restr) : {fset Var} := 
  match r with
  | NCONS v => FVArg v
  | r1 ≠ r2 => FVArg r1 `|` FVArg r2
  end.


Inductive Bind :=
  | isEQ of Arg & Arg
  | isCONS of Arg.

Definition contr  (b : Bind) (r : Restr) := 
  match r, b with
  | v ≠ u, isEQ v' u' => ((v, u) == (v', u')) || ((u, v) == (v', u'))
  | NCONS v, isCONS u => v == u
  | _, _              => false
  end.

Definition is_arg (e : Exp) := 
  if e is Exp_Arg _ then true else false.

Definition is_cons (e : Exp) := 
  if e is CONS _ _ then true else false.


Definition ncontr_neq env r1 r2 := 
    is_arg (r1 /s/ env) ->
    is_arg (r2 /s/ env) ->
    r1 /s/ env <> r2 /s/ env.

Definition ncontr_ncons env r := 
  ~~ is_cons (r /s/ env).


Definition ncontr_env (env : Env) (rs : seq Restr) := 
  (forall r1 r2, r1 ≠ r2 \in rs -> ncontr_neq env r1 r2) /\
  (forall r, NCONS r \in rs -> ncontr_ncons env r).


Definition contradict r b : bool :=
  has (contr b) r .

Definition delete_restr (v : Var) := 
  filter (fun r => match r with 
                   | (r1 ≠ r2) => (r1 != v) && (r2 != v)
                   | NCONS r => r != v
                  end).

Definition cas  (v u : Arg) (r : Restr) := 
  if r is x ≠ y then 
    (if x == v then u else x) ≠ (if y == v then u else y)
  else r.


Definition rsubst (r : seq Restr) (b : Bind) : seq Restr := 
  match b with 
  | isEQ u v => map (cas u v) r
  | isCONS _ => r
  end.

Definition of_Bind b : Env := 
  match b with 
  | isEQ (Arg_Var u) v => [fsfun emsub with u |-> Exp_Arg v]
  | _                  => emsub
  end.

Coercion of_Bind : Bind >-> Env.

Definition b2r b : Restr := 
  match b with
  | isEQ u v => u ≠ v
  | isCONS u => NCONS u
  end.
Coercion b2r : Bind >-> Restr.

Definition csubst (c : Cenv) (e : Bind) := 
  let: (ce, r) := c in
  (comp ce e, rsubst r e).

Definition restr (c : Cenv) (b : Bind) := 
  let: (e, r) := c in (e, b2r b :: r).

Lemma substE (e1 e2 : Env) : 
  (forall v : Var, v /s/ e1 = v /s/ e2) -> e1 = e2.
Proof.
by move=> E; apply/fsfunP=> [n]; move: (E n).
Qed.

Lemma substP (f : Exp -> Exp) (env : Env): 
  (forall v : Var, env v = f v) ->
  (forall a, f 'a = 'a) ->
  (forall e1 e2, f (CONS e1 e2) = CONS (f e1) (f e2)) ->
  (forall e, e /s/ env = f e).
Proof.
move=> ???; elim=> /= [[[]|?]|?->?->]//=.
Qed.

Lemma emsubv (v : Var): 
  emsub v = v.
Proof. by rewrite fsfun_dflt /= ?finsupp0 ?inE. Qed.

Lemma comp_env x e1 e2: 
  x /s/ (comp e1 e2) = (x /s/ e1) /s/ e2.
Proof.
rewrite -[(x /s/ e1) /s/ e2]/((fun y => (y /s/ e1) /s/ e2) x).
apply/substP=> // ?.
rewrite /comp fsfunE; case: ifP=> //= /negbT.
by rewrite inE negb_or => /andP[??]; rewrite fsfun_dflt //= fsfun_dflt.
Qed.

Lemma comp0e e1: comp emsub e1 = e1.
Proof. by apply/substE=> v; rewrite comp_env /= emsubv. Qed.

Lemma compe0 e1: comp e1 emsub = e1.
Proof. 
apply/substE=> v. rewrite comp_env /= -{2}[e1 v]/(id (e1 v)).
apply/substP=> //; exact/emsubv.
Qed.

Lemma compA e1 e2 e3 : comp e1 (comp e2 e3) = comp (comp e1 e2) e3.
Proof. by apply/substE=> ?; rewrite ?comp_env. Qed.

Lemma subst_var (v u : Var) (e : Exp): 
  v /s/ ([fsfun emsub with u |-> e]) = if v == u then e else v.
Proof. by rewrite /= fsfun_withE emsubv. Qed.

Lemma subst_fv e (e1 e2 : Env): 
  (forall x, x \in FVExp e -> e1 x = e2 x) ->
  e /s/ e1 = e /s/ e2.
Proof.
elim: e=> /= [[[]|?]|? IHe1 ? IHe2 H]//; first by (apply; rewrite ?inE).
by apply/congr2; rewrite (IHe1, IHe2) // => ? I; rewrite H // ?inE I ?orbT.
Qed.

Definition whole_env (e : Env)  := 
  [fset x | a in finsupp e, x in FVExp (e a)].

Lemma mem_whole_env x e: 
  reflect (exists2 y, y \in finsupp e & (x \in FVExp (e y)))
  (x \in whole_env e).
Proof.
apply/(iffP idP)=> [/imfset2P[y ? [? /[swap]<- ?]]|[y *]].
- by exists y.
apply/imfset2P; exists y=> //; by exists x.
Qed.

Definition whole_rs (rs : seq Restr) := 
  [fset x | a in rs, x in FVRestr a].

Lemma mem_whole_rs x rs: 
  reflect (exists2 y, (y \in rs) & (x \in FVRestr y))
  (x \in whole_rs rs).
apply/(iffP idP)=> [/imfset2P[y ? [? /[swap]<- ?]]|[y *]].
- by exists y.
apply/imfset2P; exists y=> //; by exists x.
Qed.

Definition whole (e : Cenv) : {fset Var} :=
  whole_env e.1 `|` whole_rs e.2.

Lemma whole_env_substin (env : Env) v: 
  v \in finsupp env ->
  FVExp (env v) `<=` whole_env env.
Proof. move=> ?; apply/fsubsetP=> ??; apply/mem_whole_env; by exists v. Qed.

Lemma whole_env_subst (env : Env) (e : Exp): 
  FVExp (e /s/ env) `<=` FVExp e `|` whole_env env.
Proof.
elim: e=> /= [[[]|v]|? IHe1 ? IHe2] //=.
- case: (boolP (v \in finsupp env))=> [?|?].
  apply/(fsubset_trans (whole_env_substin _ _ _))=> //.
  by rewrite fsubsetUr.
  by rewrite fsfun_dflt //= fsubsetUl.
rewrite fsubUset; apply/andP; split.
- apply/(fsubset_trans IHe1).
  by rewrite [FVExp _ `|` FVExp _]fsetUC -fsetUA fsubsetUr.
apply/(fsubset_trans IHe2); by rewrite -fsetUA fsubsetUr.
Qed.


Lemma whole_subst (env : Env) (rs : seq Restr) (e : Exp): 
  FVExp (e /s/ env) `<=` FVExp e `|` whole (env, rs).
Proof. by rewrite /whole fsetUA /= fsubsetU // whole_env_subst. Qed.

Lemma whole_restr {e rs r}: 
  whole (e, r :: rs) = FVRestr r `|` whole (e, rs).
Proof.
rewrite /whole /= fsetUC [whole_env _ `|` _]fsetUC fsetUA.
apply/congr2=> //; apply/fsetP=> ?; rewrite inE.
apply/(sameP idP)/(iffP idP)=> [/orP[]I|/mem_whole_rs[]].
- apply/mem_whole_rs; exists r=> //=; by rewrite inE eq_refl.
- case/mem_whole_rs: I=> y I *. apply/mem_whole_rs; exists y=> //.
  by rewrite inE orbC I.
move=> x; rewrite inE=> /orP[/eqP->-> //|??]; apply/orP; right.
by apply/mem_whole_rs; exists x.
Qed.

Lemma whole_with {env : Env} {v : Var} {e : Exp} {rs}: 
  whole ([fsfun env with v |-> e], rs) `<=` v |` (FVExp e) `|` whole (env, rs).
Proof.
rewrite -fsetUA fsubsetU //; apply/orP; right.
rewrite /whole /= fsetUA fsetSU //.
apply/fsubsetP=> ? /mem_whole_env[x].
rewrite finsupp_with; case: ifP=> [/eqP->|].
- rewrite fsfun_withE ?inE. case: ifP=> //= ???; apply/orP; right.
  by apply/mem_whole_env; exists x.
rewrite ?inE fsfun_withE; case: ifP=> //= [???->//|*]; apply/orP; right.
by apply/mem_whole_env; exists x.
Qed.

Lemma comp_var (v : Var) env env': 
  comp env env' v = (env v) /s/ env'.
Proof. by rewrite -[comp env env' v]/(v /s/ (comp env env')) comp_env. Qed.


Lemma whole_comp {env : Env} {v : Var} {e : Exp} {rs}: 
  whole (comp env [fsfun emsub with v |-> e], rs) `<=` (FVExp e) `|` whole (env, rs).
Proof.
rewrite /whole /= fsetUA fsetSU //.
apply/fsubsetP=> ? /mem_whole_env[x]; rewrite comp_var /comp.
rewrite inE=> /(fsubsetP finsupp_fsfun); rewrite inE.
case: (boolP (x \in finsupp env))=> /= [? _|?].
- move/(fsubsetP (whole_env_subst _ _)); rewrite inE=> /orP[?|].
  apply/orP; right; apply/mem_whole_env; by exists x.
- case/mem_whole_env=> ?; rewrite finsupp_with; case: ifP=> [|?].
  - by rewrite finsupp0 ?inE andbF.
  by rewrite ?inE orbF=> /eqP->; rewrite fsfun_with=>->.
rewrite finsupp_with; case: ifP; first by rewrite finsupp0 ?inE andbF.
rewrite ?inE orbF fsfun_dflt // => ? /eqP-> /=.
by rewrite fsfun_with=>->. 
Qed.

Lemma whole_cas {v a env rs}: 
  whole (env, [seq cas v a i | i <- rs]) `<=`
  FVArg a `|` whole (env, rs).
Proof.
rewrite /whole /= [FVArg _ `|` _]fsetUC -fsetUA fsetUS //.
apply/fsubsetP=> x /mem_whole_rs[y /mapP[z]].
rewrite /cas. case: z=> [r1 r2|].
- case: ifP=> [/eqP->|].
  - case: ifP=> [/eqP-> ? -> /=|]. 
    - rewrite fsetUid inE=>->; by rewrite orbT.
    move=> ?? -> /=; rewrite ?inE=> /orP[->|H]; first by rewrite orbT.
    apply/orP; left; apply/mem_whole_rs; exists (v ≠ r2)=> //=.
    by rewrite ?inE H orbT.
  - case: ifP=> [/eqP-> ?? -> /=|].
    - rewrite ?inE=> /orP[H|->]; last by rewrite orbT.
    apply/orP; left; apply/mem_whole_rs; exists (r1 ≠ v)=> //=.
    by rewrite ?inE H.
  move=> ??? -> ?; rewrite ?inE.
  apply/orP; left; apply/mem_whole_rs; by exists (r1 ≠ r2)=> //=.
move=> u ? -> /= ?; rewrite ?inE.
apply/orP; left; apply/mem_whole_rs; by exists (NCONS u)=> //=.
Qed.

Definition aux (e : Env) (f : {fset Var}): {fset Var} :=
  [fset x | a in f, x in FVExp (e a)].

Lemma mem_aux (e : Env) (f : {fset Var}) x: 
  reflect (exists2 y, y \in f & x \in FVExp (e y))
  (x \in aux e f).
Proof.
apply/(iffP idP)=> [/imfset2P[y ? [? /[swap]-> ?]]|[y ??]].
- by exists y.
apply/imfset2P; exists y=> //; by exists x.
Qed.

Lemma auxU f g e: aux e (f `|` g) = aux e f `|` aux e g.
Proof.
apply/fsetP=> ?; apply/(sameP idP)/(iffP idP); rewrite ?inE.
- by case/orP=> /mem_aux[x I ?]; apply/mem_aux; exists x=> //; rewrite ?inE I ?orbT.
case/mem_aux=> x.
by rewrite ?inE=> /orP[] I ?; apply/orP; [left | right]; apply/mem_aux; exists x.
Qed.

Lemma aux_FVExp e a : aux e (FVExp a) = FVExp a /s/ e.
Proof.
elim: a=> [|? IH1 ? IH2] /=; last by rewrite auxU IH1 IH2.
- case=> [[]?|v] //=; apply/fsetP=> ?; apply/(sameP idP)/(iffP idP).
  - by rewrite inE.
  - case/mem_aux=> ?; by rewrite inE.
  - move=> ?; apply/mem_aux; exists v=> //; by rewrite ?inE.
  by case/mem_aux=> ?; rewrite ?inE=> /eqP->.
Qed.

Lemma memNwhole k rs v env env'  e1 l: 
  max_set (whole (env, rs)) <= k ->
  v < l -> k < l ->
  (env v) /s/ [fsfun env' with l |-> e1] = 
  (env v) /s/ env'.
Proof.
move/mem_max_set=> m ??.
case: (boolP (v \in finsupp env))=> [/whole_env_substin H|?].
- have: forall x, x \in FVExp (env v) -> x <= k.
  move=> ? /(fsubsetP H) I; apply/m; by rewrite inE /= I.
  elim: (env v)=> [[[]|u /(_ _ (fset11 _))]|] //=.
  - rewrite fsfun_withE; case: ifP; slia.
  move=> ? IHe1 ? IHe2 I; rewrite IHe1 ?IHe2 //; 
  by move=> ? I'; apply/I; rewrite ?inE I' ?orbT.
rewrite fsfun_dflt //= fsfun_withE; case: ifP; slia.
Qed.

Lemma whole_cons rs (env : Env) (v : Var) e1 e2: 
  env v = CONS e1 e2 -> 
  ((FVExp e1 `<=` whole (env, rs)) * (FVExp e2 `<=` whole (env, rs)))%type.
Proof.
case: (boolP (v \in finsupp env))=> [/whole_env_substin|?].
- move=> /[swap]-> /=; rewrite fsubUset /whole /= => /andP[H1 H2].
  by rewrite ?fsubsetU // (H1, H2).
by rewrite fsfun_dflt.
Qed.

Section ContradictTh.

Lemma cont_isCONS rs v: contradict rs (isCONS v) = (NCONS v \in rs).
Proof.
elim: rs=> //= a ?; rewrite inE /contr; case: a=> // a ->; apply/orb_id2r=> ?.
by apply/(sameP _ eqP)/(iffP eqP)=> [|[]]->.
Qed.

Lemma cont_isEQ rs v u: 
  reflect (exists r1 r2, r1 ≠ r2 \in rs /\
  ((r1, r2) = (v, u) \/ (r2, r1) = (v, u)))
  (contradict rs (isEQ v u)).
Proof. 
apply/(iffP hasP)=> [[[]//= r1 r2 ?]|[r1 [r2 [?]]]] /pred2P ?.
- by exists r1, r2.
by exists (r1 ≠ r2).
Qed.

Lemma Ncont_isEQ rs v u: 
  reflect (forall r1 r2, r1 ≠ r2 \in rs ->
  ((r1, r2) <> (v, u) /\ (r2, r1) <> (v, u)))
  (~~ (contradict rs (isEQ v u))).
Proof.
apply/(iffP hasPn)=> [H ?? /H|H []// ?? /H[/eqP/[swap]/eqP]]; rewrite negb_or.
- by case/andP=>/eqP?/eqP.
by move->=>->.
Qed. 

Lemma ncontr_cons e rs v: 
  ncontr_env e (NCONS v :: rs) <->
  (ncontr_env e rs /\ ncontr_ncons e v).
Proof.
split=> [][] H1 H2; do ?split.
- by move=> ?? I; apply/H1; rewrite ?inE I orbT.
- by move=> ? I; apply/H2; rewrite ?inE I orbT.
- by apply/H2; rewrite ?inE eq_refl.
- by move=> ??; rewrite inE=> /orP[]//; case: H1=> H ? /H.
by move=> ?; rewrite inE=> /orP[/eqP[->]|]//; case: H1=> ? H /H.
Qed.

Lemma ncontr_eq e rs v u: 
  ncontr_env e (v ≠ u :: rs) <->
  (ncontr_env e rs /\ ncontr_neq e v u).
Proof.
split=> [][] H1 H2; do ?split.
- by move=> ?? I; apply/H1; rewrite ?inE I orbT.
- by move=> ? I; apply/H2; rewrite ?inE I orbT.
- by apply/H1; rewrite ?inE eq_refl.
- by move=> ??; rewrite inE=> /orP[/eqP[->->]|]//; case: H1=> H ? /H.
by move=> ?; rewrite inE=> /orP[]//; case: H1=> ? H /H.
Qed.

Lemma ncontr_whole env' env v rs e: 
  max_set (whole (env', rs)) < v ->
  ncontr_env env rs ->
  ncontr_env [fsfun env with v |-> e] rs.
Proof.
move/mem_max_set'=> H.
have: {in whole_rs rs, forall x : nat, x < v}=> [? I|{H}H].
- by apply/H; rewrite /whole /= ?inE I orbT.
case=> H1 H2; split=> [r1 r2 I|].
  - have: {subset FVRestr (r1 ≠ r2) <= whole_rs rs}.
    move=> ??; apply/mem_whole_rs; by exists (r1 ≠ r2).
  case: r1 r2 I=> [[? [[? /H1 //]|u /H1 N I]]|] /=.
  - have ?: u < v.
    - by apply/H/I=> /=; rewrite ?inE eq_refl.
    move=> ? /= /[dup] ?; rewrite fsfun_withE; case: ifP; try slia.
    move=> *; exact/N.
  move=> u [[? /H1 N I]|] /=.
    - have ?: u < v by apply/H/I=> /=; rewrite ?inE eq_refl.
      move=> /[swap] ? /= /[dup] ?; rewrite fsfun_withE; case: ifP; try slia.
    move=> *; exact/N.
  move=> u' /H1 N I .
  - have ?: u < v by apply/H/I=> /=; rewrite ?inE eq_refl.
  - have ?: u' < v by apply/H/I=> /=; rewrite ?inE eq_refl orbT.
  move=> /[dup] ? /[dup] ? /=; rewrite ?fsfun_withE; do ?case: ifP; try slia.
  move=> *; exact/N.
move=> [[]|] // u I.
have: {subset FVRestr (NCONS u) <= whole_rs rs}.
move=> ??; apply/mem_whole_rs; by exists (NCONS u).
move: I=> /[swap] /= I /H2 N.
- have ? : u < v by apply/H/I; rewrite ?inE eq_refl.
rewrite /ncontr_ncons /= fsfun_withE; case: ifP; slia.
Qed.

Lemma fmap_of0 xs: mkEnv xs [::] = emsub.
Proof. by case: xs. Qed.

Lemma fmap_ofcons v vs x xs: mkEnv (x :: xs) (v :: vs) = 
  [fsfun mkEnv xs vs with x |-> v].
Proof. by []. Qed.

Lemma whole_fmap {xs} {e : Env} {l rs}: 
  whole (mkEnv xs (map (subst^~ e) l), rs) `<=` 
  whole (e, rs) `|` [fset x | y in l, x in FVExp y].
Proof.
rewrite /whole /= [(_ `|` _)`|` _]fsetUC fsetUA fsetSU //.
apply/fsubsetP=> y /mem_whole_env [x].
elim: xs l=> [l|b l' IHxs [/=|a l /=]]. 
- rewrite /mkEnv /= . case: l=> //=; by rewrite finsupp0.
- by rewrite fmap_of0 /= finsupp0.
rewrite fmap_ofcons fsfun_withE; case: ifP=> [??|E].
- move/(fsubsetP (whole_env_subst _ _)); rewrite ?inE=> /orP[|->].
  - move=> ?; apply/orP; left; apply/imfset2P; exists a.
    - by rewrite /= mem_head.
   by exists y.  
  by rewrite orbT.
have /fsubsetP/[apply]:  
  finsupp [fsfun mkEnv l' [seq x0 /s/ e | x0 <- l] with b |-> a /s/ e] `<=`
  b |` finsupp (mkEnv l' [seq x0 /s/ e | x0 <- l]).
- rewrite finsupp_with; case: ifP=> // ?. 
  exact/(fsubset_trans (fsubD1set _ _ ))/fsubsetU1.
rewrite ?inE E /==> /IHxs /[apply]; rewrite ?inE => /orP[/imfset2P[z I [w ? ->]]|->].
- apply/orP; left. apply/imfset2P; exists z; first by rewrite ?inE I orbT.
  by exists w.
by rewrite orbT.
Qed.

Lemma subst_closed e env: closed e -> e = e /s/ env.
Proof.
elim: e=> [[[]|? /eqP /= /(congr1 (fun x => #|` x|))]|? IH1 ? IH2] //=.
- by rewrite cardfs1.
rewrite /closed /= fsetU_eq0=> /andP[??].
by apply/congr2; rewrite -(IH1, IH2).
Qed.

Lemma fmap_cat e1 e2 t:
  (forall x, x \in e1 -> closed x) ->
  size t = (size e1 + size e2)%N  ->
  mkEnv t (e1 ++ e2) =
  comp (mkEnv t e1) (mkEnv (drop (size e1) t) e2).
Proof.
elim: e1 t=> /= [?|?? IH [|?? c /=?]]; first by rewrite fmap_of0 comp0e drop0.
- slia.
rewrite ?fmap_ofcons; apply/substE=> v; rewrite comp_env /= ?fsfun_withE.
case: ifP=> ?; first (rewrite -subst_closed //; exact/c/mem_head).
rewrite IH ?comp_var // => [? I|]; last slia; apply/c; by rewrite ?inE I orbT.
Qed.

End ContradictTh.





