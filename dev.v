From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap choice finfun fintype.
From deriving Require Import deriving.
From coqspec Require Import int.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Inductive Restr := Neq of Exp & Exp.

Definition restr_indDef := [indDef for Restr_rect].
Canonical restr_indType := IndType Restr restr_indDef.

Definition restr_eqMixin := [derive eqMixin for Restr].
Canonical restr_eqType := Eval hnf in EqType Restr restr_eqMixin.

Definition br_indDef := [indDef for Branch_rect].
Canonical br_indType := IndType Branch br_indDef.

Definition br_eqMixin := [derive eqMixin for Branch].
Canonical br_eqType := Eval hnf in EqType Branch br_eqMixin.

Notation "e1 '≠' e2" := (Neq e1 e2) (at level 10).

Definition Cenv := (Env * seq Restr)%type.

Definition contr (r : Restr) := 
  match r with
  | (Arg_Var v) ≠ (Arg_Var u)   => v == u
  | (Arg_Val 'v) ≠ (Arg_Val 'u) => v == u
  | (CONS _ _) ≠   (CONS _ _)   => true
  | _                           => false
  end.

Definition delete_restr (v : Var) := 
  filter (fun '(r ≠ r') => (r != v) && (r' != v)).


Definition contradict r : bool :=
  has contr r.

(*Definition extend (c : Cenv) (b : Env) := 
  let: (e, r) := c in (e + b, r).*)


Definition rsubst (r : seq Restr) (e : Env) : seq Restr := 
  map (fun '(r1 ≠ r2) => r1 /s/ e ≠ r2 /s/ e) r.

Inductive Bind := BIND of Var & Exp.
Notation "v ↦ e" := (BIND v e) (at level 20).

Definition extend (c : Cenv) (b : Bind) : Cenv := 
  let: (ce, rs) := c in
  let: (v ↦ e)  := b in
  ([fsfun ce with v |-> e], rs).

Definition of_Bind : Bind -> Env := 
  fun '(k ↦ e) => [fsfun emsub with k |-> e].

Coercion of_Bind : Bind >-> Env.

Definition b2r : Bind -> Restr := fun '(a ↦ b) => a ≠ b.
Coercion b2r : Bind >-> Restr.

Definition csubst (c : Cenv) (e : Env) := 
  let: (ce, r) := c in
  (comp e ce, rsubst r e).

Definition restr (c : Cenv) (b : Bind) := 
  let: (e, r) := c in (e, b2r b :: r).

Inductive CBranch := 
  | CTRUE  of Cenv
  | CFALSE of Cenv
  | CBOTH  of Cntr & Cenv & Cenv.

Definition both (c : Cntr) (te fe : Cenv) (b : Bind) :=
  let: e1 := csubst te b in
  let: e2 := restr  fe b in
  if contradict e1.2 then
    CFALSE e2
  else CBOTH c e1 e2.

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
      else both (EQA? (Arg_Var a) (Arg_Var b)) ce ce (a ↦ b)
    | Arg_Var v,  Arg_Val u  => 
      both (EQA? (Arg_Var v) (Arg_Val u)) ce ce (v ↦ y')
    | Arg_Val u,  Arg_Var v  => 
      both (EQA? (Arg_Val u) (Arg_Var v)) ce ce (v ↦ x')
    | _, _                   => CBOTH (EQA? x' y') ce ce
    end
  | CONS? x h t pf =>
    let: e := extend (extend ce (t ↦ '0)) (h ↦ '0) in
    let: x' := x /s/ (e.1) in
    match x' with
    | CONS a b  => CTRUE 
      (extend (extend e (t ↦ b)) (h ↦ a))
    | Arg_Val _ => CFALSE e
    | Arg_Var v => 
       let (e0, rs) := e in
       both (CONS? v h t pf)
        ([fsfun e0 with h |->  Exp_Arg h, t |-> Exp_Arg t],
        delete_restr t (delete_restr h rs))
        ce
        (v ↦ CONS h t)
    end
  end.

Fixpoint dev (t : Tree) (e : Cenv) : Tree :=
  match t with
  | RET x        => x /s/ (e.1)
  | LET v x t    => 
    dev t (extend e (v ↦ x /s/ ([fsfun e.1 with v |-> Exp_Arg '0])))
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

Lemma comp_var e1 e2 v : comp e1 e2 v = (e1 v) /s/ e2.
Proof. Admitted.


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

Lemma rsubst2 rs e1 e2: 
 rsubst (rsubst rs e1) e2 = rsubst rs (comp e1 e2).
Proof.
rewrite /rsubst -map_comp/=; apply eq_map=> [[]]/=*; by rewrite -?comp_env.
Qed. 

Lemma contradict_rsubstP e1 rs: 
  reflect 
  (exists r1 r2, ((r1 ≠ r2) \in rs) * (contr (r1 /s/ e1 ≠ r2 /s/ e1)))%type
  (contradict (rsubst rs e1)).
Proof.
apply/(equivP hasP); split=> [[[?? /mapP[[r1 r2 ? -> ?]]]]|[r1 [r2 [*]]]].
- by exists r1, r2.
exists (r1 /s/ e1 ≠ r2 /s/ e1)=> //; by apply/mapP; exists (r1 ≠ r2).
Qed.

Lemma Ncontradict_rsubstP e1 rs: 
  reflect 
  (forall r1 r2, ((r1 ≠ r2) \in rs) -> (~~ contr (r1 /s/ e1 ≠ r2 /s/ e1)))%type
  (~~ contradict (rsubst rs e1)).
Proof.
apply/(equivP hasPn); split=> [R r1 r2 ?|R [r1 r2 /mapP[[e e0 /R + ->]]]]//.
by apply/R/mapP; exists (r1 ≠ r2).
Qed.

Lemma contradict_rsubst {e1 rs}: 
  ~~ contradict (rsubst rs e1) ->
  ~~ contradict rs.
Proof.
move/Ncontradict_rsubstP=> C; apply/hasPn=> [[++/C]].
case=> [[[]?[[[]|]|]|u[[]|]]|??[]]// v.
case: (boolP (u == v))=> [|/negbTE/=->]// /eqP->/=.
case: (e1 v)=> // [[[]|]] ?; by rewrite eq_refl.
Qed.

Lemma subst_with e1 e2 e3:
  closed_sub e2 -> 
  finsupp e3 `<=` finsupp e2 ->
  e1 /s/ e2 = (e1 /s/ e2) /s/ e3.
Proof.
move=> C /fsubsetP V.
rewrite -[(e1 /s/ e2) /s/ e3]/((fun x => (x /s/ e2) /s/ e3) e1).
apply/substP=> //= v.
case: (boolP (v \in finsupp e2))=> [/C|/[dup] /negP N N'].
- elim: (e2 v)=> [[[]|[]n /eqP/(congr1 (fun x => #|` x|))]|]//=.
- by rewrite cardfs1.
- move=> ? IHe1 ? IHe2. 
  by rewrite /closed /= fsetU_eq0=> /andP[]/IHe1{1}->/IHe2{1}->.
by rewrite fsfun_dflt //=  fsfun_dflt //; apply/negP=> /V /N.
Qed.

Lemma emsub_with (v : Var) : [fsfun emsub with v |-> Exp_Arg v] = emsub.
Proof.
by apply/substE=> /= ?; rewrite fsfun_withE emsubv; case: ifP=> [/eqP->|].
Qed.

Lemma sub_emsub e : e /s/ emsub = e.
Proof. rewrite -[e]/(id e); apply/substP=> //; exact/emsubv. Qed.


End SubstTh.

Lemma contr_symm r1 r2: 
  contr (r1 ≠ r2) = contr (r2 ≠ r1).
Proof.
case: r1 r2=> [[[]|]|??[[[]|]|]]//.
- move=> ? []// [[]|] // ? /=; exact/esym.
move=> ? []// [[]|]// ? /=; exact/esym.
Qed.

Lemma contrrr r: 
  contr (r ≠ r).
Proof. by case: r=> // [[[]|]] ? /=; rewrite eq_refl. Qed.

Lemma NCTRUEboth c e1 e2 b e3 :
  ~ both c e1 e2 b = CTRUE e3.
Proof. by rewrite /both; case: ifP. Qed.

Lemma contradict_ATOM {v : Var} {u : Arg} {e1 e2 rs e}: 
  ~~ (contradict (rsubst rs e2)) ->
  both (EQA? v u) (e1, rs) (e1, rs) (v ↦ u) = CFALSE e ->
  (~~ contr (v /s/ e2 ≠ (u /s/ e2)) * (e = (e1, v ≠ u :: rs))).
Proof.
rewrite /both; case: ifP=> // [++[->]].
case/contradict_rsubstP=> r1 [r2 [++ /Ncontradict_rsubstP I]].
move: r1 r2=> ++ /I.
case=> [[[]|]|??[[[]|?]|]]//; rewrite ?subst_var; last by case: ifP.
- move=> a [] // [[]/=? /negbTE->|] // ?; rewrite subst_var; case: ifP=> //= /eqP->.
  case: u=> // [[? + /eqP <-]] //=; case: (e2 v)=> // [[]] // [?]; by rewrite eq_sym.
move=> ? [[[]|]|]//; last (rewrite subst_var; case: ifP=> // /eqP->).
- case: u=> [|??]; last by (rewrite subst_var; case: ifP).
  by move=> []??; rewrite subst_var; case: ifP=> // /eqP-> /[swap] /eqP->.
  move=> ?; rewrite ?subst_var; case: ifP; case: ifP=> //.
  - by move/eqP->=> /eqP->; rewrite contrrr.
  - by move=> ? /eqP->; case: u=> [[]|]// ?? /eqP->.
  - by move/eqP->; case: u=> [[]|]// ? ? + /eqP<-; rewrite contr_symm.
  by move=> +++ /eqP E; rewrite E contrrr.
by case: u=> // [[]]//.
Qed.

Lemma contradict_ATOM' {v : Var} {u : Arg} {e1 e2 rs e}: 
  ~~ (contradict (rsubst rs e2)) ->
  both (EQA? u v) (e1, rs) (e1, rs) (v ↦ u) = CFALSE e ->
  (~~ contr (v /s/ e2 ≠ (u /s/ e2)) * (e = (e1, v ≠ u :: rs))).
Proof.
rewrite /both; case: ifP=> // [++[->]].
case/contradict_rsubstP=> r1 [r2 [++ /Ncontradict_rsubstP I]].
move: r1 r2=> ++ /I.
case=> [[[]|]|??[[[]|?]|]]//; rewrite ?subst_var; last by case: ifP.
- move=> a [] // [[]/=? /negbTE->|] // ?; rewrite subst_var; case: ifP=> //= /eqP->.
  case: u=> // [[? + /eqP <-]] //=; case: (e2 v)=> // [[]] // [?]; by rewrite eq_sym.
move=> ? [[[]|]|]//; last (rewrite subst_var; case: ifP=> // /eqP->).
- case: u=> [|??]; last by (rewrite subst_var; case: ifP).
  by move=> []??; rewrite subst_var; case: ifP=> // /eqP-> /[swap] /eqP->.
  move=> ?; rewrite ?subst_var; case: ifP; case: ifP=> //.
  - by move/eqP->=> /eqP->; rewrite contrrr.
  - by move=> ? /eqP->; case: u=> [[]|]// ?? /eqP->.
  - by move/eqP->; case: u=> [[]|]// ? ? + /eqP<-; rewrite contr_symm.
  by move=> +++ /eqP E; rewrite E contrrr.
by case: u=> // [[]]//.
Qed.

Lemma dev_contr_CTRUE e2 {e1 : Env}
  {rs : seq Restr} {e : Cenv} {c : Cntr}:
  (closed_sub e2) -> 
  (closed_sub (comp e1 e2)) ->
  cntr c (comp e1 e2) <> ERR ->
  dev_cntr c (e1, rs) = CTRUE e ->
  ((cntr c (comp e1 e2) = TRUE (comp e.1 e2)) *
  (e.2 = rs))%type.
Proof.
move=> CL F.
case: c => /= [[[]|????]|]//=.
  rewrite ?fsfun_withE; case: ifP=> [/eqP->|].
  - rewrite ?comp_var ?fsfun_with //=.
  case: ifP=> [/eqP-> UV1|]; first rewrite comp_var fsfun_withE UV1 fsfun_with //.
  move=> VU VV1; rewrite ?comp_var /= fsfun_withE VV1 fsfun_withE VU.
- case E: (e1 _)=> //= [a|].
  - case: a E=> [[]|?]//; rewrite /= ?fsfun_withE ?emsubv; case: ifP=> //; case: ifP=> //.
    move=> ??? + /NCTRUEboth//.
  - move=> ? [<-] /=; split=> //; apply/congr1.
  - apply/substE=> ?; rewrite ?comp_env /= ?fsfun_withE.
    case: ifP=> [/eqP<-|]. rewrite ?fsfun_with. admit.
    (*rewrite -[(_ /s/ e2) /s/ _]subst_with // -subst_with //.*)
  (*rewrite ?fsfun_withE emsubv=> ->; case: ifP=> //.*)
  (*rewrite -[(_ /s/ e2) /s/ _]subst_with // -subst_with //.*)
  admit.
rewrite ?comp_env.
case E: (_ /s/ e1)=> [[[]/=|]|]; rewrite ?comp_env //.
case E': (_ /s/ e1)=> // [[[]|]]/=.
- by case: ifP=> //= ?? [<-].
- by move=> + /NCTRUEboth.
case E': (_ /s/ e1)=> [[|]|] //.
- by move=> +/NCTRUEboth.
- case: ifP=> [/eqP-> + [<-]|? + /NCTRUEboth]//.
case E1: (_ /s/ _)=> [[][]|]; by rewrite ?eq_refl.
Admitted.

Lemma memdel r v rs: 
  r \in delete_restr v rs -> r \in rs.
Proof. by rewrite /delete_restr mem_filter=> /andP[]. Qed.

Lemma dev_contr_CFALSE e2 {e1 : Env}
  {rs : seq Restr} {e : Cenv} {c : Cntr}:
  cntr c (comp e1 e2) <> ERR ->
  ~~ contradict (rsubst rs e2) ->
  dev_cntr c (e1, rs) = CFALSE e ->
  ((cntr c (comp e1 e2) = FALSE (comp e.1 e2)) *
  ~~ contradict (rsubst e.2 e2))%type.
Proof.
case: c=> /= [??? ++ C|?? + C].
- case E: (_ /s/ e1)=> [[[]|v]|]//; rewrite ?comp_env E /=.
  - by move=> ? + [<-].
  move=> ?.
  rewrite /both; case: ifP=> //= /contradict_rsubstP[r1[r2[]]].
  move/memdel/memdel=> /[dup] I.
  move/Ncontradict_rsubstP: (C) => /[apply].
  move/contradict_rsubst: (C); rewrite /contradict -all_predC=> /allP/(_ _ I).
  case: ifP=> [?|].
  case: r1 {I}=> [[[]|]|].
  - case: r2=> [[[]/= ?? /negbTE->|]|]//.
    move=> ??; rewrite subst_var; by case: ifP.
  - case: r2=> [[[]??|v1 v2]|?? v1].
    - rewrite subst_var; by case: ifP.
    rewrite ?subst_var; case: ifP; case:ifP=> //.
    - by move=> /eqP->/eqP->/eqP.
    by move=> ?? /negbTE->.
  - rewrite subst_var; case: ifP=> // /eqP->.
  case S : (e2 v)=> [a|]//=; rewrite ?S //.
  move=> _ _ ? + [<-]; split=> //=; rewrite ?S.
  by case: a {S}=> [[]|]/=; rewrite ?S //.
- case: r2=> [[[]|]|]// ???.
  rewrite subst_var; case: ifP=> // /eqP->.
  case S : (e2 v)=> [a|]//=; rewrite ?S //.
  move=> _ _ ? + [<-]; split=> //=; rewrite S.
  by case: a {S}=> [[]|]/=.
- by rewrite emsub_with ?sub_emsub=> ? /negbTE->.
rewrite ?comp_env; case: (_ /s/ e1)=> //.
case=> [[]a|]/=.
- case: (_ /s/ e1)=> [[[]?|]|//] //=.
  - case: ifP=> // N + [<-]//.
  move=> ? + /(contradict_ATOM' C) [+ ->]/=.
  move=> /=; case: (e2 _)=> [[][]|]//=.
  move=> ? + /negbTE N; by rewrite eq_sym N.
move=> v; case: (_ /s/ e1)=> //.
- case=> [[]? H /(contradict_ATOM C)/= [E ->]|?]; last case: ifP=> // ?.
  - split=> /=; move: E H; case: (e2 _)=> //.
    - move=> [[]|]// ?; by case: ifP=> // /eqP->/eqP.
    case=> [][]// ?; rewrite negb_or C andbT=> +?; apply/implyP; rewrite implybNN.
    by apply/implyP=> /eqP->.
  move=> + /(contradict_ATOM C)/=[V->]; split=>/=.
  - move: H; case E: (e2 v)=> // [[[]|]]//=.
    - case E': (e2 _)=> // [[[]|]]//; case: ifP=> // /eqP A.
      by rewrite E E' A /= eq_refl in V.
  - move: H; case E': (e2 _)=> // [[[]|]]//=.
    case E: (e2 _)=> // [[[]|]]//; case: ifP=> // /eqP N.
    by rewrite E E' /= N eq_refl in V.
Qed.

Definition good (e : Env) := 
  forall v u : Var, v \in finsupp e -> e v = u -> u \notin finsupp e.


Lemma dev_contr_CBOTH1 {e2 e1 : Env}
  {rs rs1 : seq Restr} {ce1 : Env} {ce2 : Cenv}
  (c c1: Cntr) (e : Env): 
  (closed_sub e2) ->
  (good e1) ->
  ~~ contradict (rsubst rs e2) ->
  (cntr c (comp e1 e2)) <> ERR ->
  dev_cntr c (e1, rs) = CBOTH c1 (ce1, rs1) ce2 ->
  cntr c1 e2 = TRUE e ->
  (
    (cntr c (comp e1 e2) = TRUE (comp ce1 e)) *
    (~~ contradict (rsubst rs1 e))
  )%type.
Proof.
move=> CL C G; case: c=> /= [? v v1|??]; rewrite ?comp_env.
- case E: (_ /s/ e1)=> // [[[]|]v2] // ; rewrite /both.
  move=> /[dup] /negbTE; rewrite {1}eq_sym=> NV ?.
  case: ifP=> //= ? + [<-<-<-] /=. case E' : (e2 _)=> //=[?].
  move=> _ ? [<-]; split.
  - apply/congr1/substE=> u; rewrite ?comp_env.
    case: (boolP (u == v2))=> [/eqP->|/negbTE NE].
    - case: ifP=> [/andP[/negbTE V2V /negbTE V2V1]|NE].
      - rewrite /= fsfun_with /= fsfun_with /= fsfun_with.
        rewrite ?fsfun_withE NV eq_refl /= ?fsfun_withE NV eq_refl ?emsubv.
        rewrite V2V V2V1. admit. (* goodness *)
      - rewrite /= fsfun_with /= ?fsfun_withE emsubv; case: ifP.
        - rewrite /= fsfun_with. admit. (* e2 closed *)
        move=> V2V; rewrite V2V /= in NE; move/negbT: NE; case: ifP=> //.
        move/eqP<-; rewrite /= fsfun_withE V2V fsfun_with. admit. (* e2 closed *)
      rewrite /= ?fsfun_withE NE emsubv /= ?fsfun_withE; move: (NV). 
      case: ifP.
      - rewrite /= fsfun_with. admit. (* closed e2 *)
      case: ifP=> /=.
      - rewrite fsfun_withE NV fsfun_with. (* closed e2 *) admit.
      admit.
      admit.
case E: (_ /s/ e1)=> [[[]|]|]//=. 
- case E': (_ /s/ e1)=> [[[]|]|] //; first by case: ifP.
  - rewrite/both; case: ifP=> //= ? + [<-<-<-?/=].
    case E1: (e2 _)=> //[[[]|]]//; case: ifP=> // ? + [<-]; split.
    apply/congr1.
    apply/substE=> ?; rewrite ?comp_env /= fsfun_withE emsubv; case: ifP=> //=.
    move/eqP=>->. (* goodnes e1 *) admit. 
    admit.
- case E': (_ /s/ e1)=> /= [[[]|]|]//=.
  - rewrite /both; case: ifP=> //= ? + [<-<-<-/= ?].
    case E1: (e2 _)=> // [[[]|]]//; case: ifP=> //.
    move/eqP=> A ? [<-]; split.
    - apply/congr1/substE=> ?; rewrite ?comp_env /= fsfun_withE emsubv.
      case: ifP=> /= [/eqP->|] //. (* goodnes e1 *) admit.
    admit.
  - case: ifP=> // + ?; rewrite /both; case: ifP=> // ? + [<-<-<-]/=.
    case E1: (e2 _)=> /= [[[]|]|] //.
    - case E2: (e2 _)=> // [[[]|]]//; case: ifP=> //.
      move=> ??? [<-]. split.
      - apply/congr1/substE=> ?; rewrite ?comp_env /= fsfun_withE emsubv.
        case: ifP=> /= [/eqP->|] //. (* goodeness e1 *) admit.
      admit.
    case E2: (e2 _)=> // [[[]|]]//; case: ifP=> //.
Admitted.

Lemma dev_contr_CBOTH2 {e2 e1 : Env}
  {rs rs1 : seq Restr} {ce1 : Env} {ce2 : Cenv}
  {c c1: Cntr} {e : Env}: 
  ~~ contradict (rsubst rs e2) ->
  (cntr c (comp e1 e2)) <> ERR ->
  dev_cntr c (e1, rs) = CBOTH c1 ce2 (ce1, rs1) ->
  cntr c1 e2 = FALSE e ->
  (
    (cntr c (comp e1 e2) = FALSE (comp ce1 e)) *
    (~~ contradict (rsubst rs1 e2))
  )%type.
Proof.
move=> C; case: c=> /= [???|??]; rewrite ?comp_env.
case E: (_ /s/ e1)=> [[[]|]|]//=.
move=> ?. 
- rewrite/both; case: ifP=> //= ? + [<-?<-<-]/=.
  case: (e2 _)=> // [[[]??[<-]|??[<-]]]//.
  case: ifP=> //=.
- case: (_ /s/ e1)=> [[[]|]|]//=.
  case: (_ /s/ e1)=> [[[]|]|]//= ??; first by case:ifP.
  rewrite /both; case: ifP=> //= ? + [<-?<-<-]/=.
  case: (e2 _)=> // [[]] // [] ?; case: ifP=> [/eqP-> ?|] //.
  move=> N ? [<-]; by rewrite eq_sym N.
- case: (_ /s/ e1)=> [[[]|]|???+[<-?<-<-]]/=.
  - move=> ??; rewrite /both /=; case: ifP=> //= ? + [<-?<-<-/=].
    case: (e2 _)=> // [[]] // [] ?; by case: ifP=> // ? + [<-].
  move=> ??; case: ifP => // ? +; rewrite/both; case: ifP=> //.
  move=> N + [<-?<-<-]/=; case: (e2 _)=> [[]// []|??] //.
  by case: (e2 _)=> // [[]] // [] ??; case: ifP=> // ?? [<-].
by case: (e2 _)=> [] // [] // [] /=.
Qed.

Lemma dev_contr_CBOTH3 {e2 e1 : Env}
  {rs rs1 : seq Restr} {ce1 : Env} {ce2 : Cenv}
  {c c1: Cntr}: 
  (cntr c (comp e1 e2)) <> ERR ->
  dev_cntr c (e1, rs) = CBOTH c1 ce2 (ce1, rs1) ->
  cntr c1 e2 = ERR -> False.
Proof.
case: c=> [a??|??]/=; rewrite ?comp_env.
- case: (_ /s/ e1)=> // [[]] // ???; rewrite /both.
  by case: ifP=> // ? [<-?] /=; case: (e2 _).
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

Lemma int_dev (t : Tree) (e1 e2 : Env) (rs : seq Restr): 
  (closed_sub e2) ->
  int t (comp e1 e2) <> '0 ->
  ~~ contradict (rsubst rs e2) ->
  int t (comp e1 e2) = int (dev t (e1, rs)) e2.
Proof.
elim: t e1 e2 rs=> //= [*|t e ?|c t1 IHt1 t2 IHt2 e1 e2 ? CL C CR].
- by rewrite comp_env.
- move => IHt /= e1 e2 ?? NE ?.
  have H: [fsfun comp e1 e2 with t |-> e /s/ ([fsfun comp e1 e2 with t |-> Exp_Arg '0])] =
  comp [fsfun e1 with t |-> e /s/ ([fsfun e1 with t |-> Exp_Arg '0])] e2.
  - apply/substE=> u; rewrite comp_env /=.
    rewrite ?fsfun_withE; case: ifP=> [?|?].
    - suff ->: [fsfun comp e1 e2 with t |-> Exp_Arg ' (0)] =
            comp [fsfun e1 with t |-> Exp_Arg ' (0)] e2.
      - by rewrite comp_env.
    apply/substE=> u'; rewrite comp_env /= ?fsfun_withE; case: ifP=> //.
    - by rewrite -[comp e1 e2 u']/(u' /s/ (comp e1 e2)) comp_env.
    by rewrite -[comp e1 e2 u]/(u /s/ (comp e1 e2)) comp_env.
  by rewrite -IHt // -H.
have NE : (cntr c (comp e1 e2) <> ERR) by move: C; case: (cntr _).
case E : (dev_cntr _ _)=> [[]|[]|?[]??[]]/=.
- move/(dev_contr_CTRUE CL NE): E C=>/=[->->] ?.
  by rewrite -IHt1.
- move/(dev_contr_CFALSE e2 NE CR): E C=>/= [-> ?] ?.
  by rewrite -IHt2.
case E': (cntr _ e2).
- move: E' C=> /[dup] /(dev_contr_CBOTH1 _ CL CR NE E)[->].
  move=> ? /cntr_env_TRUE/(_ CL)[] *; by rewrite -IHt1.
- move: E' C=> /[dup] /(dev_contr_CBOTH2 CR NE E)[->].
  move=> ? /cntr_env_FALSE /eqP -> ?; by rewrite -IHt2.
by move/(dev_contr_CBOTH3 NE E): E'.
Admitted.

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
  (forall x, x \in e2 -> closed x) ->
  int_Prog p (e1 ++ e2) <> '0 ->
  int_Prog p (e1 ++ e2) = int_Prog (dev_Prog p e1) e2.
Proof. 
case: p=> /= _ ??? H ?.
by rewrite -int_dev // -?fmap_cat // => ? /codomf_fmap_of/H.
Qed.


