From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrfun seq.
From mathcomp Require Import finmap choice finfun fintype.
From coqspec Require Import int utilities substitution dev.

Definition x1    : Var   :=  1.
Definition x2    : Var   :=  2.
Definition YES   : Val   := '3.
Definition NO    : Val   := '4.
Definition h1    : Var   :=  3.
Definition h2    : Var   :=  4.
Definition t1    : Var   :=  5.
Definition t2    : Var   :=  6.
Definition h1'   : Var   :=  7.
Definition h2'   : Var   :=  8.
Definition eqStr : FName :=  1.

Notation "'If' c 'Then' t1 'Else' t2" := (COND c t1 t2) (at level 50).
Notation "'Case' x 'Of' '|' h & t '-->' t1 '|' 'ATOM' '-->' t2" := 
  (COND (CONS? x) (HT h t x t1) t2) (at level 100).
Notation "x =? y" := (EQA? x y) (at level 10).
Notation "a $ b"  := (CALL a b) (at level 10).

Definition eq_str : Def := 
  DEFINE eqStr [:: x1; x2] (
    Case x1 Of 
    | h1 & t1 --> 
        Case x2 Of
        |  h2 & t2 -->
            If h1 =? h2 Then
              eqStr $ [:: (t1 : Exp); (t2 : Exp)]
            Else NO
        |  ATOM --> NO
    | ATOM --> 
        If (CONS? x2) Then
          NO
        Else If x1 =? x2 Then
          YES
        Else NO
  ).

Arguments dev : simpl nomatch.
Arguments caller : simpl never.

Lemma example: 
  specn 2 eq_str [:: CONS '3 '4] [:: eq_str] = 
  DEFINE eqStr [:: x2] (
    Case x2 Of 
    | h1' & h2' --> 
        If '3 =? h1' Then
          If CONS? h2' Then NO
          Else If '4 =? h2' Then YES
          Else NO
        Else NO
    | ATOM --> NO).
Proof.
have H: ((fun=> id) @2` ([:: Exp_Arg t1; Exp_Arg t2], FVExp)) = [fset t1; t2].
apply/fsetP=> x.
apply/imfset2P; rewrite ?inE.
case: (boolP (x == t1))=> [/eqP->|] /=.
- exists t1=> //; exists t1=> /=; by rewrite ?inE.
case: ifP=> [/eqP->|+/negbTE+[?+[?+E]]].
- do? exists t2=> //; by rewrite ?inE.
by rewrite ?inE E=> N1 N2 /orP[]/eqP-> /=; rewrite ?inE (N1, N2).

rewrite /specn /devn /spec /= {1}/caller /=.
move=> /=.
suff->: (maxn
      (maxn (maxvar (CALL 1 [:: Exp_Arg x1; Exp_Arg x2]))
          (max_set (whole (mkEnv [:: x1; x2] [:: CONS ' (3) ' (4)], [::]))))
      (maxvar
          (If CONStest x1
          Then HT h1 t1 x1
                  (If CONStest x2
                  Then HT h2 t2 x2
                          (If ATOMtest h1 h2 Then CALL 1 [:: Exp_Arg t1; Exp_Arg t2] Else NO)
                  Else NO)
          Else (If CONStest x2 Then NO
                Else (If ATOMtest x1 x2 Then YES Else NO))))) = 6.
set f := caller [:: eq_str; eq_str] (dev id_call).
rewrite /dev.
suff->: dev_cntr (CONStest x1)
(mkEnv [:: x1; x2]
    [:: mkEnv [:: x1; x2] [:: CONS ' (3) ' (4)] x1;
        mkEnv [:: x1; x2] [:: CONS ' (3) ' (4)] x2], [::]) = 
CTRUE ([fsfun emsub with x1 |-> CONS '3 '4 ], [::]).
rewrite /subst fsfun_with.
suff->: (dev_cntr (CONStest x2)
([fsfun emsub with h1 |-> (Exp_Arg ' (3)), t1 |-> (Exp_Arg ' (4)), x1 |-> CONS ' (3) ' (4)],
[::])) = CBOTH (CONStest x2) ([fsfun emsub with h1 |->  Exp_Arg ' (3), t1 |->  Exp_Arg ' (4), x1 |-> CONS ' (3) ' (4)],
[::]) ([fsfun emsub with h1 |-> Exp_Arg ' (3), t1 |-> Exp_Arg ' (4), x1 |-> CONS ' (3) ' (4)],
[:: NCONS x2]).
rewrite ?fsfun_withE emsubv.
do 3? case: (boolP (_ == _))=> *; try slia.
have->: dev_cntr (ATOMtest h1 h2)
([fsfun emsub
  with x2 |-> CONS (Exp_Arg (Arg_Var 7)) (Exp_Arg (Arg_Var 8)), h2 |-> (Exp_Arg (Arg_Var 7)), 
        t2 |-> Exp_Arg (Arg_Var 8), h1 |-> Exp_Arg ' (3), t1 |-> Exp_Arg ' (4),
        x1 |-> CONS ' (3) ' (4)], [::]) =
        CBOTH (ATOMtest (Exp_Arg (Arg_Val ' (3))) (Exp_Arg (Arg_Var 7)))
        (comp
            [fsfun emsub
            with x2 |-> CONS (Exp_Arg (Arg_Var 7)) (Exp_Arg (Arg_Var 8)),
                  h2 |-> Exp_Arg (Arg_Var 7), t2 |-> Exp_Arg (Arg_Var 8),
                  h1 |-> Exp_Arg (Arg_Val ' (3)), t1 |-> Exp_Arg (Arg_Val ' (4)),
                  x1 |-> CONS (Exp_Arg (Arg_Val ' (3))) (Exp_Arg (Arg_Val ' (4)))]
            [fsfun emsub with 7 |-> Exp_Arg (Arg_Val ' (3))], [::])
        ([fsfun emsub
          with x2 |-> CONS (Exp_Arg (Arg_Var 7)) (Exp_Arg (Arg_Var 8)),
                h2 |-> Exp_Arg (Arg_Var 7), t2 |-> Exp_Arg (Arg_Var 8),
                h1 |-> Exp_Arg (Arg_Val ' (3)), t1 |-> Exp_Arg (Arg_Val ' (4)),
                x1 |-> CONS (Exp_Arg (Arg_Val ' (3))) (Exp_Arg (Arg_Val ' (4)))],
        [:: (Arg_Var 7) ≠ (Arg_Val ' (3))]).
rewrite /dev_cntr /subst /= ?fsfun_withE ?eq_refl.
do 3? case: (boolP (_ == _))=> * //; try slia.
rewrite /NO /id_call /= ?comp_var /= ?fsfun_withE ?eq_refl /= ?fsfun_withE emsubv.
have-> //: (8 == 7) = false by slia.
suff->:  (maxn 9
(maxvar
    (If CONStest (Arg_Var x1)
    Then HT h1 t1 x1
            (If CONStest (Arg_Var x2)
            Then HT h2 t2 x2
                    (If ATOMtest 
                          (Exp_Arg (Arg_Var h1))
                          (Exp_Arg (Arg_Var h2))
                    Then CALL 1
                            [::
                            Exp_Arg (Arg_Var t1);
                            Exp_Arg (Arg_Var t2)]
                    Else RET (Exp_Arg (Arg_Val NO)))
            Else RET (Exp_Arg (Arg_Val NO)))
    Else (If CONStest (Arg_Var x2)
          Then RET (Exp_Arg (Arg_Val NO))
          Else (If ATOMtest (Exp_Arg (Arg_Var x1))
                      (Exp_Arg (Arg_Var x2))
                Then RET (Exp_Arg (Arg_Val YES))
                Else RET (Exp_Arg (Arg_Val NO))))))) = 9.

rewrite /dev. 

have->: dev_cntr (CONStest x1)
(mkEnv [:: x1; x2] [:: Exp_Arg ' (4); Exp_Arg (Arg_Var 8)], [::]) =
CFALSE
([fsfun emsub
  with x1 |-> Exp_Arg (Arg_Val ' (4)), x2 |-> Exp_Arg (Arg_Var 8)], [::]).
- rewrite /dev_cntr /= /mkEnv /= fsfun_with //.
have->: dev_cntr (CONStest x2)
([fsfun emsub with x1 |-> Exp_Arg ' (4), x2 |-> Exp_Arg (Arg_Var 8)], [::]) = 
CBOTH (CONStest (Arg_Var 8))
(comp
    [fsfun emsub
    with x1 |-> Exp_Arg (Arg_Val ' (4)), x2 |-> Exp_Arg (Arg_Var 8)] emsub,
[::])
([fsfun emsub
  with x1 |-> Exp_Arg (Arg_Val ' (4)), x2 |-> Exp_Arg (Arg_Var 8)],
[:: NCONS (Arg_Var 8)]).
- rewrite /dev_cntr /= fsfun_withE.
  case: (boolP (_ == _)); try slia.
  rewrite fsfun_with //.
have-> //=: dev_cntr (ATOMtest x1 x2)
([fsfun emsub with x1 |-> (Exp_Arg '(4)), x2 |->  Exp_Arg (Arg_Var 8)],
[:: NCONS (Arg_Var 8)]) = CBOTH (ATOMtest (Exp_Arg (Arg_Val ' (4))) (Exp_Arg (Arg_Var 8)))
(comp
    [fsfun emsub
    with x1 |-> Exp_Arg (Arg_Val ' (4)), x2 |-> Exp_Arg (Arg_Var 8)]
    [fsfun emsub with 8 |-> Exp_Arg (Arg_Val ' (4))],
[:: NCONS (Arg_Var 8)])
([fsfun emsub
  with x1 |-> Exp_Arg (Arg_Val ' (4)), x2 |-> Exp_Arg (Arg_Var 8)],
[:: (Arg_Var 8) ≠ (Arg_Val ' (4)); NCONS (Arg_Var 8)]).
- rewrite /dev_cntr /= fsfun_with fsfun_withE.
  case: (boolP (_ == _)); try slia.
  rewrite fsfun_with //=.

rewrite /maxvar ?max_setU /= ?max_set1 H.
by rewrite max_setU /max_set ?enum_fsetE /= ?enum_fset1 /=.
rewrite /dev_cntr /= ?fsfun_withE emsubv.

do 3? case: (boolP (_ == _))=> * //; try slia.
by congr CBOTH; congr (_,_); rewrite compe0.

rewrite /dev_cntr /= /mkEnv /= ?fsfun_with ?fsfun_withE emsubv.
have->: (x2 == x1) = false by slia.

congr CTRUE; congr (_,_); apply/fsfunP=> ?.
by rewrite ?fsfun_withE emsubv; (do ? case: ifP=> //) => /eqP->.
rewrite /maxvar.

rewrite /VTree /= ?max_setU ?H ?max_set0 /= ?max_setU.
have->: ((fun=> id) @2` ([:: Exp_Arg x1; Exp_Arg x2], FVExp)) = [fset x1; x2].
apply/fsetP=> x.
apply/imfset2P; rewrite ?inE.
case: (boolP (x == x1))=> [/eqP->|] /=.
- exists x1=> //; exists x1=> /=; by rewrite ?inE.
case: ifP=> [/eqP->|+/negbTE+[?+[?+E]]].
- do? exists x2=> //; by rewrite ?inE.
by rewrite ?inE E=> N1 N2 /orP[]/eqP-> /=; rewrite ?inE (N1, N2).
rewrite max_setU ?max_set1 /whole_rs.
have->: (fun=> id) @2` ([::], FVRestr) = fset0.
apply/fsetP=> ?; apply/imfset2P; rewrite ?inE=> [[/= ?]].
by rewrite ?inE.
rewrite max_set0 /mkEnv /=.
have->: (whole_env [fsfun emsub with x1 |-> CONS ' (3) ' (4)]) = fset0.
apply/fsetP=> ?; apply/imfset2P; rewrite ?inE=> [[/= ?]].
rewrite finsupp_with /= ?inE orbF=> /eqP-> [?].
by rewrite fsfun_with /= ?inE.
by rewrite max_set0.
Qed.