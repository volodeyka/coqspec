From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap fintype choice.

Open Scope fmap_scope.
Open Scope fset_scope.

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

Lemma foldr_monoid {T : Type} {f : T -> T -> T} {n s1 s2}: 
associative f ->
(forall x, f n x = x) ->
(forall x, f x n = x) ->
f (foldr f n s1) (foldr f n s2) =
foldr f n (s1 ++ s2).
Proof. by move=> A L R; elim: s1=> //= ??; rewrite -A=>->. Qed.

Definition max_set (f : seq nat) : nat :=
  foldr maxn 0 f.

Lemma max_set0 : max_set fset0 = 0.
Proof. by []. Qed.

Lemma max_set1 x: max_set [fset x] = x.
Proof. 
by rewrite /max_set enum_fsetE enum_fset1.
Qed.

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

Lemma max_set_le {f h: {fset nat}} {k : nat}: 
  max_set f <= k -> h `<=` f ->
  max_set h <= k.
Proof. move=> ? /fsubsetP /max_subset; slia.  Qed.

Lemma max_add {f :{fset nat}} {k}: 
  max_set f <= k -> max_set ([fset k.+1; k.+2] `|` f) <= k.+3.
Proof.
move=> ?. apply/(@leq_trans (max_set (k.+1 :: k.+2 :: f))).
- apply/max_subset=> ?; by rewrite ?inE orbA.
rewrite /= ?geq_max; apply/and3P; split; slia.
Qed.

Lemma max_setU f g: 
  max_set (f `|` g) = maxn (max_set f) (max_set g).
Proof.
have->: maxn (max_set f) (max_set g) = max_set (f ++ g).
exact/(foldr_monoid maxnA max0n maxn0).
have /andP/anti_leq //: ((max_set (f `|` g) <= max_set (f ++ g)) /\ 
      (max_set (f ++ g) <= max_set (f `|` g)))%type.
split; apply/max_subset=> ?; by rewrite ?inE mem_cat.
Qed.


Lemma max_set_le2 {f g h : {fset nat}} {k}: 
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

Lemma fsfunE {K : choiceType} {V : eqType} S f y dflt: 
  ([fsfun x in S => f x] : {fsfun K -> V for dflt}) y = 
  if y \in S then f y else dflt y.
Proof. 
rewrite /fsfun_of_fun /fsfun_of_ffun Fsfun.of_ffunE.
by case: insubP=> [[/=??->->]|/negbTE->].
Qed.

Lemma finsupp_fsfun {K : eqType} {V: choiceType} {f g : V -> K} {s : {fset V}}: 
  finsupp ([fsfun x in s => f x] : {fsfun V -> K for g}) `<=` s.
Proof.
apply/fsubsetP=> ?; rewrite mem_finsupp fsfunE; case: ifP=> //.
by rewrite eq_refl.
Qed.

