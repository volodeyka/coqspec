From Coq Require Import Lia Relations.
From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap choice finfun fintype.
From deriving Require Import deriving.
From coqspec Require Import int utilities substitution.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Definition br_indDef := [indDef for Branch_rect].
Canonical br_indType := IndType Branch br_indDef.

Definition br_eqMixin := [derive eqMixin for Branch].
Canonical br_eqType := Eval hnf in EqType Branch br_eqMixin.

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

Section Spec.

Variable p : Prog.

Fixpoint dev (f : Var -> Tree -> Cenv -> Tree)
  (k : Var) (t : Tree) (e : Cenv) : Tree :=
  match t with
  | RET x        => x /s/ (e.1)
  | LET v x t    => let (e, rs) := e in
    dev f k t ([fsfun e with v |-> x /s/ e], rs)
  | HT v u x t    => let (e, rs) := e in
    match x /s/ e with
    | CONS a b =>
      dev f k t ([fsfun e with v |-> a, u |-> b], rs)
    | Arg_Var y => 
      HT (k.+1) (k.+2) y (
        dev f k.+3 t 
          ([fsfun e with 
            x |-> CONS (k.+1 : Var) (k.+2 : Var),
            v |-> Exp_Arg (k.+1 : Var),
            u |-> Exp_Arg (k.+2 : Var)], rs)
      ) 
    | _ => RET ERROR
    end
  | COND c t1 t2 => 
    match dev_cntr c e with
    | CTRUE e       => dev f k t1 e
    | CFALSE e      => dev f k t2 e
    | CBOTH c e1 e2 => COND c (dev f k t1 e1) (dev f k t2 e2)
    end
  | CALL g args => f k t e
  end.

Definition caller (f : Var -> Tree -> Cenv -> Tree) 
  (k : Var) (t : Tree) (e : Cenv) : Tree :=
  match t with
  | CALL g args => 
     let: (t, xs) := get_func g p in
     f (maxn k (maxvar t)) t (mkEnv xs [seq x /s/ (e.1) | x <- args], e.2)
  | _  => f k t e
  end.

Definition id_call (k : Var) (t : Tree) (c : Cenv):= 
  let: (e, _) := c in
  match t with
  | CALL g args => CALL g [seq x /s/ e | x <- args]
  | _ => t
  end.

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
  move=> /eqP ??; split=> //=. split=> //; apply/ncontr_eq; split=> // => ?? /=. 
  by rewrite E'=> [[/esym]].
  by rewrite whole_restr fsubUset fsubsetUr aux_EQA E''' E'' /= fsetU0 fset0U fsub1set fsetU11.
move=> /=; case E: (e2 v)=> // [[[]|]]//.
case E'''': (_ /s/ e1)=> // [[[]|u]] //.
- case: ifP=> // +++ [<-]/=.
  case: ifP=> // [/eqP<-|/eqP AA].
  - move=> /cont_isEQ[r1 [r2 [I Eq]]] ? [/(_ _ _ I)].
    by case: Eq=> [][->->]; rewrite /ncontr_neq /= E /==>/(_ erefl erefl).
  move=> *; split=> //. split=> //; apply/ncontr_eq; split=> // => ?? /=. 
  by rewrite E=> [[]].
  by rewrite whole_restr fsubUset fsubsetUr aux_EQA E''' /= E'''' /= fsetU0 fsub1set fsetU11.
move=> /=; case E': (e2 _)=> // [[[]|]] // ?.
case: ifP=> //; case: ifP=> //; case: ifP=> [/eqP AA|].
- rewrite AA in E.
  move=> /cont_isEQ[r1 [r2 [I Eq]]] ? [/(_ _ _ I)].
  by case: Eq=> [][->->]; rewrite /ncontr_neq /= E' E /==>/(_ erefl erefl).
move=> /eqP ???? []<-; split=> //=.
split=> //; apply/ncontr_eq; split=> // => ?? /=. 
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
    rewrite aux_EQA E /= fset0U. 
    by apply/(fsubset_trans whole_cas)=> /=; rewrite fset0U fsubsetUr.
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
  rewrite aux_EQA G /= fset0U R. 
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
rewrite aux_EQA R G /= fsubUset [[fset v; u]]fsetUC -fsetUA fsubsetUl /=.
by apply/(fsubset_trans whole_cas)=> /=; rewrite fsetUS // fsubsetUr.
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
  move=> /eqP N ? [<-]; split=> //. 
  split=> //; apply/ncontr_eq; split=> // => ?? /=. 
  by rewrite E=> /esym [].
  by rewrite whole_restr /= aux_EQA E' /= fsetU0 -fsetUA fsubsetUr.
case E: (e2 _)=> // [[[]|]] //.
case E': (_ /s/ e1)=> // [[[]|]] //=.
- move=> ?; case: ifP=> // ? [<-?<-<-]/=; rewrite E; case: ifP=> /eqP AA // [<-].
  split=> //. split=> //; apply/ncontr_eq; split=> // => ?? /=. 
  by rewrite E=> [[]].
  by rewrite whole_restr /= aux_EQA E'' /= fsetU0 [_ |` FVExp _]fsetUC -fsetUA fsubsetUr.
move=> /=; case E''': (e2 _)=> // [[[]|]] // ?; case: ifP=> //; case: ifP=> //.
move=> ?? [<-?<-<-] /=; rewrite E''' E; case: ifP=> // /eqP ? [<-].
split=> //. split=> //; apply/ncontr_eq; split=> // => ?? /=. 
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

Arguments whole : simpl never.

Notation well_typed := (@well_typed p).


Definition correct (f : Var -> Tree -> Cenv -> Tree) := 
  forall e1 e2 rs k g args n ,
  let: t := CALL g args in 
  int n t (comp e1 e2) p <> ERROR ->
  well_typed t -> 
  max_set (whole (e1, rs)) <= k ->
  maxvar t <= k ->
  ncontr_env e2 rs ->
  int n t (comp e1 e2) p = int n (f k t (e1, rs)) e2 p.

Arguments int : simpl never.

Hypothesis well_typed_prog : forall f, 
  ((well_typed (get_func f p).1) *
  ({subset FVTree (get_func f p).1 <= (get_func f p).2}))%type.

Lemma int_dev f e1 e2 rs k t n: 
  correct f ->
  int n t (comp e1 e2) p <> ERROR ->
  well_typed t -> 
  max_set (whole (e1, rs)) <= k ->
  maxvar t <= k ->
  ncontr_env e2 rs ->
  int n t (comp e1 e2) p = int n (dev f k t (e1, rs)) e2 p.
Proof.
have l: forall k, (k.+2 == k.+1) = false by slia.
move=> corr; move: n. 
elim: t e1 e2 rs k => // [/= +++++ n|/= v e t IHt e1 e2 rs k n|||].
1,2: case: n=> //.
- move=> *. by rewrite /int /= comp_env.
- move=> n  /=; rewrite {1 2}/int-/int.
  have <-: comp [fsfun e1 with v |-> e /s/ e1] e2 =
        [fsfun comp e1 e2 with v |-> e /s/ (comp e1 e2)].
  - apply/substE=> u; rewrite comp_env /= ?fsfun_withE.
    by case: ifP; rewrite -?[comp e1 e2 u]/(u /s/ (comp e1 e2)) comp_env.
  move=> ? /andP[??] m1 m2 *. rewrite -IHt // -1?int_not0 //.
  - apply/(max_set_le2 m2 m1)/(fsubset_trans whole_with)=> /=.
  - rewrite -?fsetUA fsetUS // fsubUset 1?fsetUA fsubsetUr -fsetUA.
    by rewrite fsetUC -fsetUA fsubsetU // fsetUC whole_subst orbT.
  by apply/(max_set_le m2)=> /=; rewrite fsetUA fsubsetUr.
move=> c t1 IHt1 t2 IHt2 e1 e2 rs k n.
case: n=> // n /=. rewrite {1 2}/int /= -/int=> C /andP[] wf1 wf2 m1 m2.
have NE : (cntr c (comp e1 e2) <> ERR) by move: C; case: (cntr _).
case E : (dev_cntr _ _)=> [[]|[]|?[]??[]]/= N.
- move/(dev_contr_CTRUE _ NE): E C=>/=[[->-> s]] ?.
  rewrite -IHt1 // -?int_not0 //.
  - apply/(max_set_le2 m2 m1)/(fsubset_trans s).
    rewrite fsubUset fsubsetUr /= andbT.
    apply/(fsubset_trans (auxE _ _ rs)).
    by rewrite fsubUset fsubsetUr -?fsetUA fsubsetUl.
  apply/(max_set_le m2)=> /=; by rewrite fsetUC fsetUA fsubsetUr.
- move/(dev_contr_CFALSE NE N): E C=>/= [[-> ? s]] ?.
  rewrite -IHt2 //-?int_not0 //.
  - apply/(max_set_le2 m2 m1)/(fsubset_trans s).
    rewrite fsubUset fsubsetUr /= andbT.
    apply/(fsubset_trans (auxE _ _ rs)).
    by rewrite fsubUset fsubsetUr -?fsetUA fsubsetUl.
    apply/(max_set_le m2)=> /=; by rewrite fsubsetUr.
rewrite /int /= -/int.
case E': (cntr _ e2).
  - move: E' C=> /[dup] /(dev_contr_CBOTH1 _ N NE E)[[->]] ? s /cntr_env_TRUE Eq ?.
    rewrite -IHt1 //.
  - apply/(max_set_le2 m2 m1)/(fsubset_trans s).
    rewrite fsubUset fsubsetUr /= andbT.
    apply/(fsubset_trans (auxE _ _ rs)).
    by rewrite fsubUset fsubsetUr -?fsetUA fsubsetUl.
  apply/(max_set_le m2)=> /=; by rewrite fsetUC fsetUA fsubsetUr.
  - move: E' C=> /[dup] /(dev_contr_CBOTH2 N NE E) [[->]] ? s /cntr_env_FALSE Eq ?.
    rewrite -IHt2  // ?Eq //.
  - apply/(max_set_le2 m2 m1)/(fsubset_trans s).
    rewrite fsubUset fsubsetUr /= andbT.
    apply/(fsubset_trans (auxE _ _ rs)).
    by rewrite fsubUset fsubsetUr -?fsetUA fsubsetUl.
    apply/(max_set_le m2)=> /=; by rewrite fsubsetUr.
  by move/(dev_contr_CBOTH3 NE E): E'.
move=> v u e t IHt e1 e2 rs k n + /and4P[/negbTE ev /negbTE eu /negbTE uv] x m' m.
case: n=> // n; rewrite {1 2}/int -/int.
rewrite comp_env /=.
case E': (e1 e) => [[[]|y]//=|e3 e4] //=.
  - rewrite /int-/int/=.
    case E: (e2 y)=> // [e3 e4].
    have ?: maxvar t <= k.
    - apply/(max_set_le m)=> /=; by rewrite fsubsetUr.
    have H: 
    int n t [fsfun comp e1 e2 with v |-> e3, u |-> e4] p =
    int n t (comp [fsfun e1 with 
            e |-> CONS (Exp_Arg (k.+1 : Var)) (Exp_Arg (k.+2 : Var)),
            v |-> Exp_Arg (k.+1 : Var),
            u |-> Exp_Arg (k.+2 : Var)]
         [fsfun e2 with k.+1 |-> e3, k.+2 |-> e4]) p.
    apply/int_maxvar=> // ??.
    - rewrite comp_var /= ?fsfun_withE; case: ifP.
      - by move/eqP->; rewrite eq_sym ev /= fsfun_with.
      case: ifP=> [/eqP-> UV|].
      - by rewrite [u == e]eq_sym eu /= fsfun_withE l fsfun_with.
      case: ifP=> [/eqP->|vy vu vv] /=.
      - rewrite fsfun_with fsfun_withE l fsfun_with.
        by rewrite -[comp e1 e2 e]/(e /s/ (comp e1 e2)) comp_env /= E' /= E.
      rewrite ?(memNwhole k rs) // ?comp_var //; slia.
    move=> ??. rewrite -IHt -?H => //; try slia.
    have m2: maxvar (HT v u e t) <= k.+3 by slia.
    apply/(max_set_le2 (max_add m') m2)/(fsubset_trans whole_with)=> /=.
    rewrite [e |` _]fsetUC fsubUset -4?fsetUA ?fsetUS //=.
    apply/(fsubset_trans whole_with)=> /=.
    rewrite [[fset v; _]]fsetUC -fsetUA fsetUS // fsetUC [[fset v; u]]fsetUC //.
    rewrite [[fset u; v] `|` _]fsetUC 3?fsetUA fsetSU //.
    apply/(fsubset_trans whole_with)=> //=.
    rewrite [[fset u; _]]fsetUC -3?fsetUA fsetUS // fsetUC 2?fsetUA fsetSU //.
    rewrite -fsetUA fsubsetUl //.
    by rewrite [e |` _]fsetUC ?fsetUA fsubsetUr.
  apply/(ncontr_whole e1); try slia.
  apply/(ncontr_whole e1); by slia.
have->: [fsfun comp e1 e2 with v |-> e3 /s/ e2, u |-> e4 /s/ e2] =
        comp [fsfun e1 with v |-> e3, u |-> e4] e2.
apply/substE=> ?; rewrite /= ?fsfun_withE; case: ifP=> [/eqP->|].
- by rewrite comp_var fsfun_with.
case: ifP=> [/eqP-> UV|VU VV];
by rewrite ?comp_var ?fsfun_withE ?eq_refl ?UV ?VV ?VU.
move=> ??. rewrite -IHt -?int_not0 //.
case/(whole_cons rs): E'=> H1 H2.
apply/(max_set_le2 m m')/(fsubset_trans whole_with)=> /=.
rewrite -?fsetUA fsetUS // fsubUset; apply/andP; split.
- apply/(fsubset_trans H1); by rewrite 2?fsetUA fsubsetUr.
apply/(fsubset_trans whole_with).
rewrite -?fsetUA fsetUS // fsubUset; apply/andP; split.
- apply/(fsubset_trans H2); by rewrite fsetUA fsubsetUr.
by rewrite fsetUA fsubsetUr.
apply/(max_set_le m)=> /=; by rewrite fsubsetUr.
move=> g ? e1 e2 ?? [] //= n *.
by rewrite -corr.
Qed.

Lemma correct_dev f : 
  correct f -> correct (caller (dev f)).
Proof.
move=> corr e1 e2 rs k g l /= [] //=.
rewrite {1 2}/int /= -/int; case E: (get_func g p)=> [vs xs] //=.
rewrite /maxvar => n N /eqP ++ m2; move=> /= S  m1 ?.
have ?: well_typed vs by rewrite -[vs]/((vs, xs).1) -E well_typed_prog.
have H: 
  int n vs (mkEnv xs [seq x /s/ (comp e1 e2) | x <- l]) p =
  int n.+1 vs (comp (mkEnv xs [seq x /s/ e1 | x <- l]) e2) p.
- rewrite int_not0 //; apply/int_freevar => // x.
  case: (well_typed_prog g)=> ?; rewrite E /==> /[apply].
  elim: xs l {E N m2} S=> //= ?? IHxs [] //= ?? [/IHxs IH].
  rewrite ?fmap_ofcons ?inE ?comp_var ?fsfun_withE.
  case: ifP=> //=; first by rewrite comp_env.
  move=> ? /IH->; by rewrite comp_var.
rewrite -int_dev ?leq_max ?leqnn ?orbT // -?H //.
by apply/orP; left; apply/(max_set_le2 m1 m2)/(fsubset_trans whole_fmap).
Qed.



Lemma correct_id: correct id_call.
Proof.
move=> ???? g l [] //= ? N /eqP S ? m *; rewrite /int/=-/int.
case E: (get_func g p)=> [t xs]. 
have ?: well_typed t by rewrite -[t]/((t, xs).1) -E well_typed_prog.
apply/int_freevar=> //; rewrite -[t]/((t, xs).1) -?E=> ? /=.
case: (well_typed_prog g)=> ? /[apply]; rewrite E /=.
rewrite E /= in S.
elim: xs l {E N m} S=> //= ?? IHxs [] //= ?? [/IHxs IH].
rewrite ?fmap_ofcons ?inE ?comp_var ?fsfun_withE.
case: ifP=> //; by rewrite comp_env.
Qed.

Definition devn n := iter n (caller \o dev) id_call.

Lemma correct_devn n:
  correct (devn n).
Proof. elim: n=> [|?]; [exact/correct_id | exact/correct_dev]. Qed.

End Spec.

Definition int_Prog n (main : Def) (p : Prog) (xs : seq Exp) : Exp := 
  let: DEFINE f vs t := main in 
    int n t (mkEnv vs xs) p.

Definition spec f (main : Def) (xs : seq Exp) : Def := 
  let: DEFINE g vs t := main in 
  let: cenv := (mkEnv vs xs, [::]) in 
  let t' := (CALL g (map (Exp_Arg \o Arg_Var) vs)) in
  DEFINE g (drop (size xs) vs) (f 
    (maxn (maxvar t') (max_set (whole cenv)))
   t'
    cenv
  ).

Definition well_typed_prog p := 
  forall f,
  ((@well_typed p (get_func f p).1) *
  ({subset FVTree (get_func f p).1 <= (get_func f p).2}))%type.


Lemma int_call n t f vs e p: 
  well_typed_prog (DEFINE f vs t :: p) ->
  int n t e (DEFINE f vs t :: p) = 
  int n.+1 (CALL f [seq (Exp_Arg \o Arg_Var) i | i <- vs]) e (DEFINE f vs t :: p).
Proof.
move=> wf.
case: n=> [/=|/=n]; rewrite ?eq_refl; first by case: t wf.
apply: (int_freevar _ _ _ n.+1); move: (wf f); rewrite /=eq_refl/==> [[]] //.
move=> _ /[swap] ? /[apply].
elim: vs  {wf}=> //= ??.
by rewrite fmap_ofcons ?inE fsfun_withE; case: ifP=> // /eqP->.
Qed.

Arguments int : simpl nomatch.


Lemma int_spec (p : Prog) (main : Def) (e1 e2 : seq Exp) f:
  let: (DEFINE _ vs main_t) := main in
  (size e1 + size e2)%N = size vs ->
  (forall x, x \in e1 -> closed x) ->
  well_typed_prog (main :: p) ->
  correct (main :: p) f ->
  forall n,
  int_Prog n main (main :: p) (e1 ++ e2) <> ERROR ->
  int_Prog n main (main :: p) (e1 ++ e2) = 
  int_Prog n.+1 (spec f main e1) (main :: p) e2.
Proof. 
case: main => /= ? l ? H ?? corr n.
rewrite fmap_cat //= => ?. 
by rewrite -corr -?int_call //= ?eq_refl /= ?size_map // leq_max ?leqnn ?orbT.
Qed.

Definition specn m f e p := 
     spec (devn (f :: p) m) f e.

Arguments specn /.

Theorem int_devn_Prog (p : Prog) (main : Def) (e1 e2 : seq Exp) m:
  let: (DEFINE _ vs main_t) := main in
  (size e1 + size e2)%N = size vs ->
  (forall x, x \in e1 -> closed x) ->
  well_typed_prog (main :: p) ->
  forall n,
  int_Prog n main (main :: p) (e1 ++ e2) <> ERROR ->
  int_Prog n main (main :: p) (e1 ++ e2) = 
  int_Prog n.+1 (specn m main e1 p) (main :: p) e2.
Proof.
case: main=> *. 
apply/(int_spec p (DEFINE _ _ _))=> //.
exact/correct_devn.
Qed.

