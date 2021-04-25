From Coq Require Import Lia Relations.
From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap choice finfun fintype.
From deriving Require Import deriving.
From coqspec Require Import int.

Ltac ssrnatify_rel :=
 match goal with
  (* less or equal (also codes for strict comparison in ssrnat) *)
  | H : is_true (leq _ _) |- _ => move/leP: H => H
  | H : context [ is_true (leq ?a ?b)] |- _ =>
     rewrite <- (rwP (@leP a b)) in H
  | |- is_true (leq _ _) => apply/leP
  | |- context [ is_true (leq ?a ?b)] => rewrite <- (rwP (@leP a b))
  (* Boolean equality *)
  | H : is_true (@eq_op _ _ _) |- _ => move/eqP: H => H
  | |- is_true (@eq_op _ _ _) => apply/eqP
  | H : context [ is_true (@eq_op _ _ _)] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ is_true (@eq_op _ ?x ?y)] => rewrite <- (rwP (@eqP _ x y))
  (* Negated boolean equality *)
  | H : is_true (negb (@eq_op _  _ _)) |- _ => move/eqP: H => H
  | |- is_true (negb (@eq_op _  _ _)) => apply/eqP
  | H : context [ is_true (negb (@eq_op _ _ _))] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ is_true (negb (@eq_op _ ?x ?y))] =>
     rewrite <- (rwP (@eqP _ x y))
  | H : (negb (@eq_op _  _ _)) = true |- _ => move/eqP: H => H
  | |- (negb (@eq_op _  _ _)) = true => apply/eqP
  | H : context [ (negb (@eq_op _ _ _)) = true ] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ (negb (@eq_op _ ?x ?y)) = true ] =>
     rewrite <- (rwP (@eqP _ x y))

  | H : (leq _ _) = true |- _ => move/leP: H => H
  | H : context [ (leq ?a ?b) = true] |- _ =>
     rewrite <- (rwP (@leP a b)) in H
  | |- (leq _ _) = true => apply/leP
  | |- context [(leq ?a ?b) = true] => rewrite <- (rwP (@leP a b))
  (* Boolean equality *)
  | H : (@eq_op _ _ _) = true |- _ => move/eqP: H => H
  | |- (@eq_op _ _ _) = true => apply/eqP
  | H : context [(@eq_op _ _ _) = true] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [(@eq_op _ ?x ?y) = true] => rewrite <- (rwP (@eqP _ x y))

  (* Negated lt *)
  | H : is_true (negb (leq (S _) _)) |- _ => move: H; rewrite -leqNgt=> H
  | H : context [ is_true (negb (leq (S _) _))] |- _ =>
     rewrite -leqNgt in H
  | |- is_true (negb (leq (S _) _)) => rewrite -leqNgt
  | |- context [ is_true (negb (leq (S _) _))] => rewrite -leqNgt

  (* Negated leq *)
  | H : is_true (negb (leq _ _)) |- _ => move: H; rewrite -ltnNge=> H
  | H : context [ is_true (negb (leq _ _))] |- _ =>
     rewrite -ltnNge in H
  | |- is_true (negb (leq _ _)) => rewrite -ltnNge
  | |- context [ is_true (negb (leq _ _))] => rewrite -ltnNge

   (* = flase *)
  | H : (_ = false) |- _ => move/negbT: H => H
  | |- (_ = false) => apply/negP
  | H : context [ (?a = false)] |- _ =>
     rewrite <-  (rwP (@negP a)) in H
  | |- context [ ?a = false] =>
     rewrite <- (rwP (@negP a))

 end.


(* Converting ssrnat operation to their std lib analogues *)
Ltac ssrnatify_op :=
 match goal with
  (* subn -> minus *)
  | H : context [subn _ _] |- _ => rewrite -!minusE in H
  | |- context [subn _ _] => rewrite -!minusE
  (* addn -> plus *)
  | H : context [addn _ _] |- _ => rewrite -!plusE in H
  | |- context [addn _ _] => rewrite -!plusE
  (* muln -> mult *)
  | H : context [muln _ _] |- _ => rewrite -!multE in H
  | |- context [muln _ _] => rewrite -!multE
 end.

(* Preparing a goal to be solved by lia by translating every formula *)
(* in the context or the conclusion which expresses a constraint on *)
(* some nat into the std lib, Prop, analogues *)
Ltac ssrnatify :=
  repeat progress ssrnatify_rel;
  repeat progress ssrnatify_op.

(* Preprocessing + lia *)
Ltac slia := try (move=> * //=); do [ ssrnatify; lia | exfalso; ssrnatify; lia].


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

Section Spec.

Variable p : Programm.

Definition max_set (f : seq Var) : Var :=
  foldr maxn 0 f.

Fixpoint VTree (t : Tree) : {fset Var} :=
  match t with
  | RET e        => FVExp e
  | LET v x t    => v |` (FVExp x `|` VTree t)
  | COND c t1 t2 => FVCntr c `|` VTree t1 `|` VTree t2
  | HT v u x t   => [fset v; u; x] `|`  (VTree t)
  | CALL f xs    => seq_fset tt xs
  end.

Definition maxvar (t : Tree) : Var := max_set (VTree t).

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
    | _ => RET '0
    end
  | COND c t1 t2 => 
    match dev_cntr c e with
    | CTRUE e       => dev f k t1 e
    | CFALSE e      => dev f k t2 e
    | CBOTH c e1 e2 => COND c (dev f k t1 e1) (dev f k t2 e2)
    end
  | CALL g args =>
    let: (t, xs) := get_func g p in
      f (maxn k (maxvar t)) t (fmap_of xs (map e.1 args), e.2)
  end.


Lemma max_set0 : max_set fset0 = 0.
Proof. by []. Qed.

Lemma max_setin g x: 
  x \in g -> x <= max_set g.
Proof.
elim: g=> //= a l IH; rewrite ?inE leq_max=> /orP[/eqP->|/IH->]; 
by rewrite (leqnn, orbT).
Qed.

Lemma max_subset f g: {subset f <= g} -> max_set f <= max_set g.
Proof.
elim: f g=> //= a f IH g s; rewrite geq_max; apply/andP; split.
- exact/max_setin/(s a)/mem_head.
by apply/IH=> ? I; apply/s; rewrite inE I orbT.
Qed.

Lemma max_set_le {f h: {fset Var}} {k : Var}: 
  max_set f <= k -> h `<=` f ->
  max_set h <= k.
Proof. move=> ? /fsubsetP /max_subset; slia.  Qed.

Lemma max_add {f :{fset Var}} {k}: 
  max_set f <= k -> max_set ([fset k.+1; k.+2] `|` f) <= k.+3.
Proof.
move=> ?. apply/(@leq_trans (max_set (k.+1 :: k.+2 :: f))).
- apply/max_subset=> ?; by rewrite ?inE orbA.
rewrite /= ?geq_max; apply/and3P; split; slia.
Qed.

Lemma foldr_monoid {T : Type} {f : T -> T -> T} {n s1 s2}: 
  associative f ->
  (forall x, f n x = x) ->
  (forall x, f x n = x) ->
  f (foldr f n s1) (foldr f n s2) =
  foldr f n (s1 ++ s2).
Proof. by move=> A L R; elim: s1=> //= ??; rewrite -A=>->. Qed.

Lemma max_setU f g: 
  max_set (f `|` g) = maxn (max_set f) (max_set g).
Proof.
have->: maxn (max_set f) (max_set g) = max_set (f ++ g).
exact/(foldr_monoid maxnA max0n maxn0).
have /andP/anti_leq //: ((max_set (f `|` g) <= max_set (f ++ g)) /\ 
      (max_set (f ++ g) <= max_set (f `|` g)))%type.
split; apply/max_subset=> ?; by rewrite ?inE mem_cat.
Qed.


Lemma max_set_le2 {f g h : {fset Var}} {k}: 
  max_set f <= k -> max_set g <= k -> h `<=` f `|` g ->
  max_set h <= k.
Proof.
move=> s1 s2 ?.
by apply/(@max_set_le (f `|` g))=> //; rewrite max_setU geq_max s1 s2.
Qed.

Lemma mem_max_set f k:
  max_set f <= k -> {in f, forall x, x <= k}.
Proof. move=> ?? /max_setin; slia. Qed.

Lemma mem_max_set' f k:
  max_set f < k -> {in f, forall x, x < k}.
Proof. move=> ?? /max_setin; slia. Qed.


(*Definition dev_Prog (f : Prog) (e : seq Exp) := 
  let: DEFINE n vs t := f in
  let: s := size e in
  DEFINE n (drop s vs) (dev (maxvar t) t (fmap_of vs e, [::])).*)

Section SubstTh.

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


Lemma fsfunE {K : choiceType} {V : eqType} S f y dflt: 
  ([fsfun x in S => f x] : {fsfun K -> V for dflt}) y = 
  if y \in S then f y else dflt y.
Proof. 
rewrite /fsfun_of_fun /fsfun_of_ffun Fsfun.of_ffunE.
by case: insubP=> [[/=??->->]|/negbTE->].
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

End SubstTh.

Definition FVRestr (r : Restr) : {fset Var} := 
  match r with
  | NCONS v => FVArg v
  | r1 ≠ r2 => FVArg r1 `|` FVArg r2
  end.

Section FreeValTh.

Lemma finsupp_fsfun {s : {fset Var}} {f : Var -> Exp}: 
  finsupp ([fsfun x in s => f x] : {fsfun Var -> Exp for id}) `<=` s.
Proof.
apply/fsubsetP=> ?; rewrite mem_finsupp fsfunE; case: ifP=> //.
by rewrite eq_refl.
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

Fixpoint well_typed (t : Tree) : bool := 
  match t with 
  | RET _ => true
  | LET v x t => well_typed t
  | COND c t1 t2 =>  well_typed t1 && well_typed t2 
  | HT v u x t => [&& x != v, x != u, v != u & well_typed t]
  | CALL f xs => size xs == size (get_func f p).2
  end.

Arguments whole : simpl never.

Lemma subst_max (e1 e2 : Env) (e : Exp) : 
  (forall x, x <= maxvar e -> e1 x = e2 x) ->
  e /s/ e1 = e /s/ e2.
Proof.
elim: e=> [[[]|?]|? IHe1 ? IHe2 I] //=; first apply.
- rewrite /maxvar /=; apply/max_setin; by rewrite ?inE.
  by rewrite IHe1 ?IHe2 //; move=> ? I'; apply/I; rewrite /maxvar /=;
rewrite max_setU leq_max I' ?orbT.
Qed.

Definition correct (f : Var -> Tree -> Cenv -> Tree) := 
  forall e1 e2 rs k t n, 
  int n t (comp e1 e2) p <> '0 ->
  well_typed t -> 
  max_set (whole (e1, rs)) <= k ->
  maxvar t <= k ->
  ncontr_env e2 rs ->
  int n t (comp e1 e2) p = int n (f k t (e1, rs)) e2 p.

Lemma int_freevar (e1 e2 : Env) t n: 
  (forall x, x \in FVTree t -> e1 x = e2 x) ->
  int n t e1 p = int n t e2 p.
Proof.
Admitted.

Lemma int_maxvar (e1 e2 : Env) t n: 
  (forall x, x <= maxvar t -> e1 x = e2 x) ->
  int n t e1 p = int n t e2 p.
Proof.
elim: t e1 e2 n=> [??? n *|??? IHt ?? n I|c ? IHt1 ? IHt2 ++ n|?? v ? IHt e1 e2 n I|++++ n].
all: case: n=> // n /=.
- exact/subst_max.
- apply/IHt=> ?. rewrite ?fsfun_withE /maxvar/= => l; case:ifP=> [/eqP ?|?].
  - apply/subst_max=> ?; rewrite /maxvar /= => m; apply/I.
    by rewrite /maxvar /= ?max_setU ?leq_max m ?orbT.
  by apply/I; rewrite /maxvar /= ?max_setU ?leq_max l ?orbT.
- case: c=> [[[a ?? I]|v e1 e2 I]|] /=.
  - apply/IHt2=> ?; rewrite /maxvar /= => I'; apply/I.
    by rewrite /maxvar /= ?max_setU ?leq_max I' ?orbT.
  - have->: e1 v = e2 v.
    - apply/I; rewrite /maxvar /= ?max_setU ?leq_max.
      by rewrite max_setin // /FVCntr /= ?inE.
    by case E: (e2 v); [apply/IHt2 | apply/IHt1]; move=> ?; rewrite /maxvar /= =>I';
    apply/I; rewrite /maxvar /= ?max_setU ?leq_max I' ?orbT.
  move=> e e' e1 e2 I.
  have->: (e /s/ e1 = e /s/ e2).
  - apply/subst_max=> ?; rewrite /maxvar /==> I'.
    by apply/I; rewrite /maxvar /= ?max_setU ?leq_max I' ?orbT.
  case: (e /s/ e2)=> // [[[]|]] //= ?.
  have->: (e' /s/ e1 = e' /s/ e2).
  - apply/subst_max=> ?; rewrite /maxvar /==> I'.
    by apply/I; rewrite /maxvar /= ?max_setU ?leq_max I' ?orbT.
  by case: (e' /s/ e2)=> // [[]] // [?]; case: ifP=> ?;
  [apply/IHt1 | apply/IHt2]; move=> ?; rewrite /maxvar /= =>I';
  apply/I; rewrite /maxvar /= ?max_setU ?leq_max I' ?orbT.
have->: e1 v = e2 v.
- apply/I.
  rewrite /maxvar /= ?max_setU ?leq_max [v <= max_set [fset v]]max_setin ?orbT //.
  by rewrite ?inE.
case: (e2 v)=> // ??; apply/IHt=> ?; rewrite /maxvar /= => I'.
rewrite ?fsfun_withE; do? case: ifP=>//.
by move=> *; apply/I; rewrite /maxvar /= ?max_setU ?leq_max I' ?orbT.
move=> f l e1 e2 IH.
case: (get_func f p)=> ? xs.
have-> //: (fmap_of xs [seq e1 i | i <- l]) =  (fmap_of xs [seq e2 i | i <- l]).
apply/congr1/eq_in_map=> ??. apply/IH.
by rewrite /maxvar /= max_setin // mem_sort_keys.
Qed.

Lemma int_not0 n t e: 
  int n t e p <> '0 ->
  int n t e p = int n.+1 t e p.
Proof. Admitted.


Lemma l k: (k.+2 == k.+1) = false.
Proof. by apply/eqP=> /esym /n_Sn. Qed.

Arguments int : simpl never.

Hypothesis well_typed_prog : forall f, 
  ((well_typed (get_func f p).1) *
  ({subset FVTree (get_func f p).1 <= (get_func f p).2}))%type.

Lemma whole_fmap {xs} {e : Env} {l rs}: 
  whole (fmap_of xs (map e l), rs) `<=` 
  whole (e, rs) `|` (seq_fset tt l).
Proof. Admitted.

Lemma fmap_of0 xs: fmap_of xs [::] = emsub.
Proof. by case: xs. Qed.

Lemma fmap_ofcons v vs x xs: fmap_of (x :: xs) (v :: vs) = 
  [fsfun fmap_of xs vs with x |-> v].
Proof.
  rewrite /fmap_of /=.
Qed.


Lemma int_dev (*(t : Tree) (e1 e2 : Env) (rs : seq Restr)*) f: 
  correct f -> correct (dev f).
  (*well_typed t -> max_set (whole (e1, rs)) <= k ->
  maxvar t <= k ->
  int t (comp e1 e2) <> '0 ->
  ncontr_env e2 rs ->
  int t (comp e1 e2) = int (dev k t (e1, rs)) e2.*)
Proof.
move=> corr * e1 e2 rs k t.
elim: t e1 e2 rs k => // [/= +++++ n|/= v e t IHt e1 e2 rs k n|||].
1,2: case: n=> //.
- move=> *. by rewrite /int /= comp_env.
- move=> n  /=; rewrite {1 2}/int-/int.
  have <-: comp [fsfun e1 with v |-> e /s/ e1] e2 =
        [fsfun comp e1 e2 with v |-> e /s/ (comp e1 e2)].
  - apply/substE=> u; rewrite comp_env /= ?fsfun_withE.
    by case: ifP; rewrite -?[comp e1 e2 u]/(u /s/ (comp e1 e2)) comp_env.
  move=> ? wf m1 m2 *. rewrite -IHt // -1?int_not0 //.
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
    apply/int_maxvar=> ??.
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

move=> g l e1 e2 ?? [] // n. rewrite {1 2}/int -/int /=.
case E: (get_func g)=> [vs xs]; rewrite /maxvar => N /= /eqP S  m1 m2 ?.
have H: 
  int n vs (fmap_of xs [seq comp e1 e2 i | i <- l]) p =
  int n.+1 vs (comp (fmap_of xs [seq e1 i | i <- l]) e2) p.
- rewrite int_not0 //; apply/int_freevar=> x.
  case: (well_typed_prog g)=> ?; rewrite E /==> /[apply].
  elim: xs l {E N m2} S=> //= ??? []//=.
  case: l {m2}=> //=; first rewrite fmap_of0 comp_var emsubv.
rewrite -corr -?H ?leq_max /maxvar ?leqnn ?orbT // => //=.
- by rewrite -[vs]/((vs, xs).1) -E well_typed_prog.
by apply/orP; left; apply/(max_set_le2 m1 m2)/(fsubset_trans whole_fmap).
Qed.

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
  well_typed t ->
  int_Prog p (e1 ++ e2) <> '0 ->
  int_Prog p (e1 ++ e2) = int_Prog (dev_Prog p e1) e2.
Proof. 
case: p=> /= _ l ?? H ??; rewrite -int_dev // -?fmap_cat //.
have/eqP->: whole (fmap_of l e1, [::]) == fset0; last by rewrite max_set0.
rewrite /whole /= fsetU_eq0 -?fsubset0.
apply/andP; split; apply/fsubsetP=> x /imfset2P[? //] /codomf_fmap_of/H /eqP->.
by case.
Qed.

Definition x1  : Var := 1.
Definition x2  : Var := 2.
Definition yes : Val := '3.
Definition no  : Val := '4.

Notation "'If' c 'Then' t1 'Else' t2" := (COND c t1 t2) (at level 30).

Definition example : Prog := 
  DEFINE 1 [:: x1; x2] 
    (If (CONS? x1) Then
      (If (CONS? x2) Then
        yes
      Else no)
    Else
      (If (CONS? x2) Then
        no
      Else yes)).

Lemma dev_example : 
  dev_Prog example [:: CONS '3 '4] = 
  DEFINE 1 [:: x2] (If (CONS? x2) Then yes Else no).
rewrite /example /= /fmap_of /= ?comp_var ?fsfun_with /= ?comp_var fsfun_withE.
have->: x2 == x1 = false by slia.
by rewrite ?emsubv /= ?emsubv.
Qed.


