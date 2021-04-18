From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap choice finfun fintype.
From deriving Require Import deriving.
From coqspec Require Import int.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Inductive Restr := 
  | Neq of Arg & Arg
  | NCONS of Arg.

Definition restr_indDef := [indDef for Restr_rect].
Canonical restr_indType := IndType Restr restr_indDef.

Definition restr_eqMixin := [derive eqMixin for Restr].
Canonical restr_eqType := Eval hnf in EqType Restr restr_eqMixin.

Definition restr_choiceMixin := [derive choiceMixin for Restr].
Canonical restr_choiceType := Eval hnf in ChoiceType Restr restr_choiceMixin.

Definition br_indDef := [indDef for Branch_rect].
Canonical br_indType := IndType Branch br_indDef.

Definition br_eqMixin := [derive eqMixin for Branch].
Canonical br_eqType := Eval hnf in EqType Branch br_eqMixin.

Notation "e1 '≠' e2" := (Neq e1 e2) (at level 10).

Definition Cenv := (Env * seq Restr)%type.

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

Inductive CBranch := 
  | CTRUE  of Cenv
  | CFALSE of Cenv
  | CBOTH  of Cntr & Cenv & Cenv.

Definition both (c : Cntr) (ce : Cenv) (b : Bind) :=
  let: (e, rs) := ce in
  if contradict rs b then
    CFALSE (restr ce b)
  else CBOTH c (csubst ce b) (restr ce b).


Definition dev_cntr (c : Cntr) (ce : Cenv) : CBranch :=
  match c with
  | EQA? x y => 
    let: x' := x /s/ (ce.1) in
    let: y' := y /s/ (ce.1) in
    match x', y' with
    | Arg_Val 'a, Arg_Val 'b => if a == b then CTRUE ce else CFALSE ce
    | Arg_Var a,  Arg_Var b  => 
      if a == b then 
        CTRUE ce 
      else both (EQA? (Arg_Var a) (Arg_Var b)) ce (isEQ a b)
    | Arg_Var v,  Arg_Val u  => 
      both (EQA? (Arg_Var v) (Arg_Val u)) ce (isEQ v u)
    | Arg_Val u,  Arg_Var v  => 
      both (EQA? (Arg_Val u) (Arg_Var v)) ce (isEQ v u)
    | _, _                   => CBOTH (EQA? x' y') ce ce
    end
  | CONS? x =>
    let: x' := x /s/ (ce.1) in
    match x' with
    | CONS a b  => CTRUE ce
    | Arg_Val _ => CFALSE ce
    | Arg_Var v => both (CONS? v) ce (isCONS v)
    end
  end.


Fixpoint dev (t : Tree) (e : Cenv) : Tree :=
  match t with
  | RET x        => x /s/ (e.1)
  | LET v x t    => let (e, rs) := e in
    dev t ([fsfun e with v |-> x /s/ e], rs)
  | HT v u pf x t    => let (e, rs) := e in
    match x /s/ e with
    | CONS a b =>
      dev t ([fsfun e with v |-> a, u |-> b], rs)
    | Arg_Var y => 
      HT v u pf y (
        dev t ([fsfun e with x |-> CONS v u, v |-> Exp_Arg v, u |-> Exp_Arg u], rs)
      )
    | _ => RET '0
    end
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
  DEFINE n (drop s vs) (dev t (fmap_of vs e, [::])).

Section SubstTh.

Lemma substE (e1 e2 : Env) : 
  (forall v : Var, v /s/ e1 = v /s/ e2) -> e1 = e2.
Proof.
by move=> E; apply/fsfunP=> [[n]]; move: (E (VAR n)).
Qed.

Lemma substP (f : Exp -> Exp) (env : Env): 
  (forall v : Var, env v = f v) ->
  (forall a, f 'a = 'a) ->
  (forall e1 e2, f (CONS e1 e2) = CONS (f e1) (f e2)) ->
  (forall e, e /s/ env = f e).
Proof.
move=> ???; elim=> /= [[[]|?]|?->?->]//=.
Qed.


Lemma fsfunE {K : choiceType} {V : eqType} S f y dflt: 
  ([fsfun x in S => f x] : {fsfun K -> V for dflt}) y = 
  if y \in S then f y else dflt y.
Proof. 
rewrite /fsfun_of_fun /fsfun_of_ffun Fsfun.of_ffunE.
by case: insubP=> [[/=??->->]|/negbTE->].
Qed.

Lemma emsubv v: 
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

End SubstTh.

Definition FVRestr (r : Restr) : {fset Var} := 
  match r with
  | NCONS v => FVArg v
  | r1 ≠ r2 => FVArg r1 `|` FVArg r2
  end.

Section FreeValTh.

Definition whole (e : Cenv) : {fset Var} :=
  [fset x | a in finsupp e.1, x in FVExp (e.1 a)] `|`
  [fset x | a in e.2, x in FVRestr a].

Lemma whole_subst (env : Env) (rs : seq Restr) (e : Exp): 
  FVExp (e /s/ env) `<=` FVExp e `|` whole (env, rs).
Proof. Admitted.

Lemma whole_restr {e rs r}: 
  whole (e, r :: rs) = FVRestr r `|` whole (e, rs).
Proof. Admitted.

Lemma whole_with {env : Env} {v : Var} {e : Exp} {rs}: 
  whole ([fsfun env with v |-> e], rs) `<=` v |` (FVExp e) `|` whole (env, rs).
Proof. Admitted.

Lemma whole_comp {env : Env} {v : Var} {e : Exp} {rs}: 
  whole (comp env [fsfun emsub with v |-> e], rs) `<=` v |` (FVExp e) `|` whole (env, rs).
Proof. Admitted.

Lemma whole_cas {v a env rs}: 
  whole (env, [seq cas v a i | i <- rs]) `<=`
  FVArg a `|` whole (env, rs).
Proof. Admitted.

Lemma whole_var (env : Env) (e : Exp) (v : Var) rs: 
  e /s/ env = v -> 
  v \in FVExp e `|` whole (env, rs).
Proof. Admitted.

(*Lemma fv_env e env : 
  FVExp (e /s/ env) `<=` 
  FVExp e `|` [fset x | a in finsupp env, x in FVExp (env a)] .
Proof.
elim: e=> [[[]?|[]]|] /=.
- 
Qed.*)

Lemma FVExp_var (v : Var): FVExp v = [fset v].
Proof. by case: v. Qed.

Definition aux (e : Env) (f : {fset Var}): {fset Var} . Admitted.

Lemma aux_CONS e a: 
  aux e (FVCntr (CONS? a)) = FVExp (a /s/ e).
Proof. Admitted.

Lemma aux_EQA e a1 a2: 
  aux e (FVCntr (EQA? a1 a2)) = FVExp (a1 /s/ e) `|` FVExp (a2 /s/ e).
Proof. Admitted.

Lemma auxE e c rs: 
  aux e (FVCntr c) `<=` FVCntr c `|` whole (e, rs).
Proof. Admitted.

Lemma memNwhole rs v env env'  e1 u: 
  u \notin whole (env, rs) ->
  (v == u) = false ->
  (env v) /s/ [fsfun env' with u |-> e1] = 
  (env v) /s/ env'.
Proof. Admitted.

Lemma whole_cons rs (env : Env) (v : Var) e1 e2: 
  env v = CONS e1 e2 -> 
  ((FVExp e1 `<=` whole (env, rs)) * (FVExp e2 `<=` whole (env, rs)))%type.
Proof. Admitted.

Lemma FVExp_cons (v u : Var) : FVExp (CONS u v) = [fset u; v].
Proof. by case: u; case: v. Qed.

Lemma comp_var (v : Var) env env': 
  comp env env' v = (env v) /s/ env'.
Proof. by rewrite -[comp env env' v]/(v /s/ (comp env env')) comp_env. Qed.

End FreeValTh.

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
  ncontr_env e (v ≠ u :: rs) =
  (ncontr_env e rs /\ ncontr_neq e v u).
Proof.
(*split=> [][] H1 H2; do ?split.
- by move=> ?? I; apply/H1; rewrite ?inE I orbT.
- by move=> ? I; apply/H2; rewrite ?inE I orbT.
- by apply/H2; rewrite ?inE eq_refl.*) Admitted.

Lemma ncontr_whole env' env v rs e: 
  v \notin whole (env', rs) ->
  ncontr_env env rs ->
  ncontr_env [fsfun env with v |-> e] rs.
Proof. Admitted.

End ContradictTh.

Arguments FVCntr : simpl never.

Lemma dev_contr_CTRUE e2 {e1 : Env}
  {rs : seq Restr} {e : Cenv} {c : Cntr}:
  cntr c (comp e1 e2) <> ERR ->
  dev_cntr c (e1, rs) = CTRUE e ->
  ((cntr c (comp e1 e2) = TRUE (comp e.1 e2)) *
  (e.2 = rs) *
  (whole e `<=` (aux e1 (FVCntr c)) `|` whole (e1, rs)))%type.
Proof.
case: c => /= ??. rewrite ?comp_env.
- case E: (_ /s/ e1)=> //= [a|].
  - case: a E=> // ??; by case: ifP.
  - move=> [<-] /=; split=> //.
  by rewrite fsubsetUr.
rewrite ?comp_env.
case E: (_ /s/ e1)=> [[[]/=|]|]; rewrite ?comp_env //.
case E': (_ /s/ e1)=> // [[[]|]]/=.
- by case: ifP=> //= ?? [<-] /=; rewrite fsubsetUr.
- by case: ifP.
case E': (_ /s/ e1)=> [[|]|] //.
- by case: ifP.
- case: ifP=> [/eqP-> + [<-]|?]//; last by case: ifP.
case E1: (_ /s/ _)=> [[][]|]; by rewrite ?eq_refl /= fsubsetUr.
Qed.

Lemma dev_contr_CFALSE e2 {e1 : Env}
  {rs : seq Restr} {e : Cenv} {c : Cntr}:
  cntr c (comp e1 e2) <> ERR ->
  ncontr_env e2 rs ->
  dev_cntr c (e1, rs) = CFALSE e ->
  ((cntr c (comp e1 e2) = FALSE (comp e.1 e2)) *
  ncontr_env e2 e.2 *
  (whole e `<=` (aux e1 (FVCntr c)) `|` whole (e1, rs)))%type.
Proof.
case: c=> /= [?|??]; rewrite ?comp_env.
- case E: (_ /s/ e1)=> [[[]|v]|]//=.
  - by move=> ?? [<-]; split=> //=; rewrite fsubsetUr.
    case: ifP=> // +++ [<-]/=.
  case E': (e2 v)=> /=.
  - rewrite cont_isCONS=> + ? /[dup] nc [?] H.
    move/H=> {H}H; split=> //. split=> //; apply/ncontr_cons=> //.
    by rewrite whole_restr fsubUset fsubsetUr aux_CONS E /= fsub1set fsetU11.
  rewrite cont_isCONS=>  I ? [? /(_ _ I)].
  by rewrite /ncontr_ncons /= E'.
rewrite ?comp_env; case E''': (_ /s/ e1)=> // [[[]a|v]].
- case E'': (_ /s/ e1)=> [[[]?|v]|//] //=.
  - by case: ifP=> // N + ? [<-]; split=> //=; rewrite fsubsetUr.
  case: ifP=> // /cont_isEQ[r1 [r2 [I Eq]]] ++[<-]/=.
  case E': (e2 v)=> // [[[]|]] //; case: ifP=> [/eqP AA ? [/(_ _ _ I)]|].
  - rewrite -AA in E'.
    by case: Eq=> [][->->]; rewrite /ncontr_neq /= E' /==>/(_ erefl erefl).
  move=> /eqP ??; split=> //. rewrite (ncontr_eq, fsubsetUr) //; (do? split=> //) => ?? /=. 
  by rewrite E'=> [[/esym]].
  by rewrite whole_restr fsubUset fsubsetUr aux_EQA E''' E'' /= fsetU0 fset0U fsub1set fsetU11.
move=> /=; case E: (e2 v)=> // [[[]|]]//.
case E'''': (_ /s/ e1)=> // [[[]|u]] //.
- case: ifP=> // +++ [<-]/=.
  case: ifP=> // [/eqP<-|/eqP AA].
  - move=> /cont_isEQ[r1 [r2 [I Eq]]] ? [/(_ _ _ I)].
    by case: Eq=> [][->->]; rewrite /ncontr_neq /= E /==>/(_ erefl erefl).
  move=> *; split=> //. rewrite (ncontr_eq, fsubsetUr) //; (do? split=> //) => ?? /=. 
  by rewrite E=> [[]].
  by rewrite whole_restr fsubUset fsubsetUr aux_EQA E''' /= E'''' /= fsetU0 fsub1set fsetU11.
move=> /=; case E': (e2 _)=> // [[[]|]] // ?.
case: ifP=> //; case: ifP=> //; case: ifP=> [/eqP AA|].
- rewrite AA in E.
  move=> /cont_isEQ[r1 [r2 [I Eq]]] ? [/(_ _ _ I)].
  by case: Eq=> [][->->]; rewrite /ncontr_neq /= E' E /==>/(_ erefl erefl).
move=> /eqP ???? []<-; split=> //=.
rewrite (ncontr_eq, fsubsetUr) //; (do? split=> //) => ?? /=. 
by rewrite E E'=> [[]].
by rewrite whole_restr fsubUset fsubsetUr aux_EQA /= E''' E'''' /= fsubsetUl.
Qed.

Lemma dev_contr_CBOTH1 {e2 e1 : Env}
  {rs rs1 : seq Restr} {ce1 : Env} {ce2 : Cenv}
  (c c1: Cntr) (e : Env): 
  ncontr_env e2 rs ->
  (cntr c (comp e1 e2)) <> ERR ->
  dev_cntr c (e1, rs) = CBOTH c1 (ce1, rs1) ce2 ->
  cntr c1 e2 = TRUE e ->
  (
    (cntr c (comp e1 e2) = TRUE (comp ce1 e)) *
    (ncontr_env e rs1) *
    (whole (ce1, rs1) `<=` (aux e1 (FVCntr c)) `|` whole (e1, rs))
  )%type.
Proof.
case: c=> /= [a|??]; rewrite ?comp_env.
- case: (a /s/ e1)=> // [[[]|]] // ?; case: ifP=> // ? /=.
  case E: (e2 _).
  - move=> ?? [<-<-<-]/=; by rewrite E.
  move=> ?? [<-<-<-]/=; rewrite E compe0 => ? []<-; split=> //.
  by rewrite fsubsetUr.
case R: (_ /s/ e1)=> // [[[]|v]]//=.
case E: (_ /s/ e1)=> [[[]|v]|] //= C; first by case: ifP.
- case E': (e2 _)=> // [[[]a1|]] // ?; case: ifP=> // C' [<-<-<-?]/=.
  rewrite E'; case: ifP=> // /eqP/[dup] ? -> [<-]; split; first split.
  - apply/congr1/substE=> ?; rewrite ?comp_env.
    suff {1}->: e2 = comp [fsfun emsub with v |-> Exp_Arg 'a1] e2.
    - by rewrite comp_env.
    apply/substE=> u; rewrite comp_env /= fsfun_withE emsubv; case: ifP=> //.
    by move/eqP->.
  - split=> // [??|?] /mapP[][]//=.
    - move=> ??; case: ifP=> [/eqP A1V I|].
      - case: ifP=> // [/eqP A2V[->->]| ].
        - by case: C=> /(_ _ _ I); rewrite A1V A2V /ncontr_neq /= E' /=.
        move=> ? [->-> ? H].
        by case: C=> /(_ _ _ I); rewrite /ncontr_neq A1V /= E' /==> /(_ erefl H).
      case: ifP=> [/eqP-> ? I [->-> H ?]|]/=.
      - by case: C=> /(_ _ _ I); rewrite /ncontr_neq /= E' => /(_ H erefl).
      move=> ?? I [->->] H1 H2.
      by case: C=> /(_ _ _ I H1 H2).
    by move=> ? I [->]; case: C=> ? /(_ _ I).
    apply/(fsubset_trans whole_comp).
    rewrite aux_EQA E /= fsetU0 fsubUset [_ `|` [fset v]]fsetUC fsub1set -fsetUA fsetU11 /=.
    by apply/(fsubset_trans whole_cas)=> /=; rewrite fset0U fsetUA fsubsetUr.
case E: (e2 _)=> // [[[]|]] //.
case G: (_ /s/ e1)=> // [[[]a1|u]] //=.
- move=> + a; case: ifP=> // C C' [<-<-<-?]/=.
  rewrite E; case: ifP=> // /eqP A [<-]; split; first split.
  - apply/congr1/substE=> ?; rewrite ?comp_env.
    suff {1}->: e2 = comp [fsfun emsub with v |-> Exp_Arg 'a1] e2.
    - by rewrite comp_env.
    apply/substE=> u; rewrite comp_env /= fsfun_withE emsubv; case: ifP=> //.
    by move/eqP->; rewrite -A.
    split=> // [??|?] /mapP[][]//=.
  - move=> ??; case: ifP=> [/eqP A1V I|].
    - case: ifP=> // [/eqP A2V[->->]| ].
      - by case: C'=> /(_ _ _ I); rewrite A1V A2V /ncontr_neq /= E A /=.
      move=> ? [->-> ? H].
      by case: C'=> /(_ _ _ I); rewrite /ncontr_neq A1V /= E A /==> /(_ erefl H).
    case: ifP=> [/eqP-> ? I [->-> H ?]|]/=.
    - by case: C'=> /(_ _ _ I); rewrite /ncontr_neq /= E A => /(_ H erefl).
    move=> ?? I [->->] H1 H2.
    by case: C'=> /(_ _ _ I H1 H2).
  by move=> ? I [->]; case: C'=> ? /(_ _ I).
  apply/(fsubset_trans whole_comp).
  rewrite aux_EQA G /= fsetU0 R /= fsubUset fsetU0 fsub1set fsetU11 /=.
  by apply/(fsubset_trans whole_cas)=> /=; rewrite fset0U fsubsetUr.
case E': (e2 u)=> // [[[]|]] // +?; case: ifP=> //; case: ifP=> //.
move=> C ? C' [<-<-<-?]/=.
rewrite E E'; case: ifP=> // /eqP A [<-]; split; first split.
- apply/congr1/substE=> ?; rewrite ?comp_env.
 suff {1}->: e2 = comp [fsfun emsub with v |-> Exp_Arg u] e2.
  - by rewrite comp_env.
  apply/substE=> ?; rewrite comp_env /= fsfun_withE emsubv; case: ifP=> //.
  by move/eqP->; rewrite /= E E' A.
  split=> // [??|?] /mapP[][]//=.
- move=> ??; case: ifP=> [/eqP A1V I|].
  - case: ifP=> // [/eqP A2V[->->]| ].
    - by case: C'=> /(_ _ _ I); rewrite A1V A2V /ncontr_neq /= E A -E' /=.
    move=> ? [->-> ? H].
    by case: C'=> /(_ _ _ I); rewrite /ncontr_neq A1V /= E A E' /==> /(_ erefl H).
  case: ifP=> [/eqP-> ? I [->-> H ?]|]/=.
  - by case: C'=> /(_ _ _ I); rewrite /ncontr_neq /= E A E' => /(_ H erefl).
  move=> ?? I [->->] H1 H2.
  by case: C'=> /(_ _ _ I H1 H2).
by move=> ? I [->]; case: C'=> ? /(_ _ I).
apply/(fsubset_trans whole_comp)=> /=.
rewrite aux_EQA R G /= fsubUset fsubsetUl /=.
by apply/(fsubset_trans whole_cas)=> /=; rewrite [[fset v; u]]fsetUC -fsetUA fsetUS // fsubsetUr.
Qed.

Lemma dev_contr_CBOTH2 {e2 e1 : Env}
  {rs rs1 : seq Restr} {ce1 : Env} {ce2 : Cenv}
  {c c1: Cntr} {e : Env}: 
  ncontr_env e2 rs ->
  (cntr c (comp e1 e2)) <> ERR ->
  dev_cntr c (e1, rs) = CBOTH c1 ce2 (ce1, rs1) ->
  cntr c1 e2 = FALSE e ->
  (
    (cntr c (comp e1 e2) = FALSE (comp ce1 e)) *
    (ncontr_env e2 rs1) *
    (whole (ce1, rs1) `<=` (aux e1 (FVCntr c)) `|` whole (e1, rs))
  )%type.
Proof.
move=> C; case: c=> /= [?|??]; rewrite ?comp_env.
case E: (_ /s/ e1)=> [[[]|]|]//=.
move=> ?. 
- case: ifP=> //= + [<-?<-<-]/=.
  case E': (e2 _)=> // ? [<-]; split=> //. rewrite ?fsubsetUr //; split=> //.
  apply/ncontr_cons.
  split=> //; by rewrite /ncontr_ncons /= E'.
  by rewrite whole_restr /= aux_CONS E /=.
- case E'': (_ /s/ e1)=> [[[]|v]|]//=.
  case E': (_ /s/ e1)=> [[[]|]|]//= ?; first by case:ifP.
  rewrite /both; case: ifP=> //=  + [<-?<-<-]/=.
  case E: (e2 _)=> // [[[]|]] //; case: ifP=> [/eqP-> ?|] //.
  move=> /eqP N ? [<-]; split=> //. rewrite (ncontr_eq, fsubsetUr) //.
  split=> //; split=> // ?? /=; by rewrite E=> /esym [].
  by rewrite whole_restr /= aux_EQA E' /= fsetU0 -fsetUA fsubsetUr.
case E: (e2 _)=> // [[[]|]] //.
case E': (_ /s/ e1)=> // [[[]|]] //=.
- move=> ?; case: ifP=> // ? [<-?<-<-]/=; rewrite E; case: ifP=> /eqP AA // [<-].
  split=> //. rewrite (ncontr_eq, fsubsetUr) //; split=> //.
  by split=> // ?? /=; rewrite E=> [[]].
  by rewrite whole_restr /= aux_EQA E'' /= fsetU0 [_ |` FVExp _]fsetUC -fsetUA fsubsetUr.
move=> /=; case E''': (e2 _)=> // [[[]|]] // ?; case: ifP=> //; case: ifP=> //.
move=> ?? [<-?<-<-] /=; rewrite E''' E; case: ifP=> // /eqP ? [<-].
split=> //. rewrite (ncontr_eq, fsubsetUr) //; split=> //; split=> // ??.
by rewrite /= E E'''=> [[]].
by rewrite whole_restr /= aux_EQA E'' E' /=.
Qed.

Lemma dev_contr_CBOTH3 {e2 e1 : Env}
  {rs rs1 : seq Restr} {ce1 : Env} {ce2 : Cenv}
  {c c1: Cntr}: 
  (cntr c (comp e1 e2)) <> ERR ->
  dev_cntr c (e1, rs) = CBOTH c1 ce2 (ce1, rs1) ->
  cntr c1 e2 = ERR -> False.
Proof.
case: c=> [a|??]/=; rewrite ?comp_env.
- case: (_ /s/ e1)=> // [[]] // ?; rewrite /both.
  by case: ifP=> // ?? [<-?] /=; case: (e2 _).
case: (_ /s/ e1)=> // [[[]|]]/=.
- case: (_ /s/ e1)=> []// [[]|]/= ??; first by case: ifP.
- rewrite /both; case: ifP => // ? + [<-?] /=.
  case: (e2 _)=> // [[]] // [] ?; by case: ifP.
case: (_ /s/ e1)=> [[[]|]|???+[<-]] /=.
- move=> ??; rewrite /both; case: ifP=> // ? + [<-]/=.
  case: (e2 _)=> // [[]] // [] ?; by case: ifP.
- move=> ??; case: ifP=> // ?; rewrite /both; case: ifP=> // ? + [<-] /=.
  case: (e2 _)=> // [[]] // [] ?; case: (e2 _)=> // [[]] // [] ?.
  by case: ifP.
by case: (e2 _).
Qed.

Fixpoint well_typed (t : Tree) (e : {fset Var}) : bool := 
  match t with 
  | RET _ => true
  | LET v x t => well_typed t (v |` FVExp x `|` e)
  | COND c t1 t2 => 
     well_typed t1 (FVCntr c `|` e) &&
     well_typed t2 (FVCntr c `|` e)
  | HT v u _ x t => 
    [&& x != v, x != u,
        v \notin e, u \notin e &
        well_typed t (v |` (u |` (x |` e)))]
  end.

Lemma well_typed_subset e2 {e1 : {fset Var}} {t}:
  e1 `<=` e2 ->
  well_typed t e2 -> well_typed t e1.
Proof.
elim: t e1 e2=> //= [??? IH ??? /IH|c? IHt1 ? IHt2 ? e2 ? /andP[/IHt1 H1 /IHt2 H2]|].
- by apply; rewrite fsetUS.
- by rewrite (IHt1 _ (FVCntr c `|` e2)) 1?(IHt2 _ (FVCntr c `|` e2)) ?fsetUS ?(H1, H2).
move=> ????? IH ?? /[dup]/fsubsetP S? /and5P[->->] /negP H1 /negP H2 /IH H /=.
by rewrite H ?fsetUA ?fsetUS // andbT; apply/andP; split; apply/negP=> /S.
Qed.

Arguments whole : simpl never.


Lemma int_dev (t : Tree) (e1 e2 : Env) (rs : seq Restr): 
  well_typed t (whole (e1, rs)) ->
  int t (comp e1 e2) <> '0 ->
  ncontr_env e2 rs ->
  int t (comp e1 e2) = int (dev t (e1, rs)) e2.
Proof.
elim: t e1 e2 rs => // [*|/= v e t IHt e1 e2 rs wf||].
- by rewrite /= comp_env.
- have <-: comp [fsfun e1 with v |-> e /s/ e1] e2 =
        [fsfun comp e1 e2 with v |-> e /s/ (comp e1 e2)].
  - apply/substE=> u; rewrite comp_env /= ?fsfun_withE.
    by case: ifP; rewrite -?[comp e1 e2 u]/(u /s/ (comp e1 e2)) comp_env.
  move=> *; rewrite -IHt //.
  apply/(well_typed_subset _ _ wf)/(fsubset_trans whole_with).
  by rewrite -?fsetUA fsetUS // fsubUset ?fsubsetUr whole_subst.
move=> c t1 IHt1 t2 IHt2 e1 e2 rs /= /andP[] wf1 wf2 C.
have NE : (cntr c (comp e1 e2) <> ERR) by move: C; case: (cntr _).
case E : (dev_cntr _ _)=> [[]|[]|?[]??[]]/= N.
- move/(dev_contr_CTRUE _ NE): E C=>/=[[->-> s]] ?.
  rewrite -IHt1 //. apply/(well_typed_subset _ s).
  apply/(well_typed_subset _ _ wf1).
  by rewrite fsubUset auxE fsubsetUr.
- move/(dev_contr_CFALSE NE N): E C=>/= [[-> ? s]] ?.
  rewrite -IHt2 //. apply/(well_typed_subset _ s).
  apply/(well_typed_subset _ _ wf2).
  by rewrite fsubUset auxE fsubsetUr.
case E': (cntr _ e2).
  - move: E' C=> /[dup] /(dev_contr_CBOTH1 _ N NE E)[[->]] ? s /cntr_env_TRUE Eq ?.
    rewrite -IHt1 //. apply/(well_typed_subset _ s).
    apply/(well_typed_subset _ _ wf1).
  by rewrite fsubUset auxE fsubsetUr.
  - move: E' C=> /[dup] /(dev_contr_CBOTH2 N NE E) [[->]] ? s /cntr_env_FALSE Eq ?.
    rewrite -IHt2  // ?Eq //. apply/(well_typed_subset _ s).
    apply/(well_typed_subset _ _ wf2).
    by rewrite fsubUset auxE fsubsetUr.
  by move/(dev_contr_CBOTH3 NE E): E'.
move=> v u /[dup] /negbTE nvu ? e t IHt e1 e2 rs /=.
move=> /and5P[/negbTE yv /negbTE yu ve1 une1 s].
rewrite -[comp e1 e2 e]/(e /s/ (comp e1 e2)) comp_env /=.
case E': (e1 e)=> /= [[[]|y]|e3 e4] //=.
  - case E: (e2 y)=> // [e3 e4].
    have->: [fsfun comp e1 e2 with v |-> e3, u |-> e4] =
        (comp [fsfun e1 with e |-> CONS v u, v |-> Exp_Arg v, u |-> Exp_Arg u]
              [fsfun e2 with v |-> e3, u |-> e4]).
    - apply/substE=> v0; rewrite comp_env /= ?fsfun_withE; case: ifP.
      - by move/eqP->; rewrite eq_sym yv /= fsfun_with.
      case: ifP=> [/eqP-> UV|].
      - by rewrite [u == e]eq_sym yu /= fsfun_withE UV fsfun_with.
      case: ifP=> [/eqP->|vy vu vv] /=.
      - rewrite fsfun_with fsfun_withE [u == v]eq_sym nvu fsfun_with.
        by rewrite -[comp e1 e2 e]/(e /s/ (comp e1 e2)) comp_env /= E' /= E.
      by rewrite ?(memNwhole rs) // -[comp e1 e2 v0]/(v0 /s/ (comp e1 e2)) comp_env.
    move=> ??; rewrite -IHt=> //.
    apply/(well_typed_subset _ _ s)/(fsubset_trans whole_with)=> /=.
    rewrite fsubUset [e |` _]fsetUC -?fsetUA ?fsetUS //= ?fsub1set ?fsetU11 //.
    apply/(fsubset_trans whole_with)=> /=.
    rewrite fsubUset fsubUset fsub1set fsetU11 /= fsetUA [[fset v; u]]fsetUC fsetUA.
    apply/(fsubset_trans whole_with)=> /=.
    by rewrite fsetSU ?fsub1set // fsubUset -fsetUA fsubsetUl.
    by apply/(ncontr_whole e1)=> //; apply/(ncontr_whole e1).
have->: [fsfun comp e1 e2 with v |-> e3 /s/ e2, u |-> e4 /s/ e2] =
        comp [fsfun e1 with v |-> e3, u |-> e4] e2.
apply/substE=> ?; rewrite /= ?fsfun_withE; case: ifP=> [/eqP->|].
- by rewrite comp_var fsfun_with.
case: ifP=> [/eqP-> UV|VU VV];
by rewrite ?comp_var ?fsfun_withE ?eq_refl ?UV ?VV ?VU.
move=> ??. rewrite -IHt=> //.
case/(whole_cons rs): E'=> H1 H2.
apply/(well_typed_subset _ _ s).
apply/(fsubset_trans whole_with). 
rewrite -fsetUA fsetUS // fsubUset; apply/andP; split.
- by apply/(fsubset_trans H1); rewrite fsetUA fsubsetUr.
apply/(fsubset_trans whole_with).
rewrite -fsetUA fsetUS // fsubUset fsubsetUr andbT; apply/(fsubset_trans H2).
by rewrite fsubsetUr.
Qed.

Lemma foldr_monoid {T : Type} {f : T -> T -> T} {n s1 s2}: 
  associative f ->
  (forall x, f n x = x) ->
  (forall x, f x n = x) ->
  f (foldr f n s1) (foldr f n s2) =
  foldr f n (s1 ++ s2).
Proof. by move=> A L R; elim: s1=> //= ??; rewrite -A=>->. Qed.


Lemma fmap_cat e1 e2 t:
  size t = (size e1 + size e2)%N  ->
  fmap_of t (e1 ++ e2) =
  comp (fmap_of t e1) (fmap_of (drop (size e1) t) e2).
Proof.
  move=> E.
  rewrite /fmap_of (foldr_monoid compA comp0e compe0); apply/congr1.
  rewrite -map_cat -{1}(cat_take_drop (size e1) t) zip_cat.
  apply/congr1/congr2=> //.
  - rewrite -{3}(cats0 e1) -{2}(cat_take_drop (size e1) t) zip_cat.
    by case: (drop _)=> /=; rewrite cats0.
all: by rewrite size_takel // E -{1}(addn0 (size e1)) leq_add2l leq0n. 
Qed.

Theorem int_dev_Prog (p : Prog) (e1 e2 : seq Exp):
  let: DEFINE n vs t := p in
  (size e1 + size e2)%N = size vs ->
  (forall x, x \in e1 -> closed x) ->
  well_typed t fset0 ->
  int_Prog p (e1 ++ e2) <> '0 ->
  int_Prog p (e1 ++ e2) = int_Prog (dev_Prog p e1) e2.
Proof. 
case: p=> /= _ l ?? H ??; rewrite -int_dev // -?fmap_cat //.
have/eqP-> //: whole (fmap_of l e1, [::]) == fset0.
rewrite /whole /= fsetU_eq0 -?fsubset0.
apply/andP; split; apply/fsubsetP=> x /imfset2P[? //] /codomf_fmap_of/H /eqP->.
by case.
Qed.


