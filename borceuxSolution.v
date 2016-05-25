(*+ borceuxSolution.v +*)

(** 
 * To program (<<encode/enrich>>) categories,  one shall memo that the common assumption that
 * catC( - , X ) is dual to catC( Y , - )
 * which originates from describing the composition as some binary operation form instead of as some functional form,
 * is FALSIFIED,
 * then get some new thing which is named <<polymorphism>> (some <<programmed naturality>>) from which to define any <<polymorph category>> and any <<polymorph functor>> and any <<polymorph transformation>>,
 * then immediately precisely describe and deduce the <<yoneda lemma>>
 * http://lpaste.net/164220
 **)

Set Implicit Arguments.

Variable obV : Type.
Variable arrV00 : obV -> obV -> Type.
Notation "V(0 V1 |- V2 )0" := (arrV00 V1 V2) (at level 30).

Variable IdenV : forall {V}, V(0 V |- V )0.
Notation "1" := (@IdenV _) (at level 0).
Variable ComV : forall UCom V3, V(0 UCom |- V3 )0 -> forall V1, V(0 V1 |-  UCom )0 -> V(0 V1 |- V3 )0.
Notation "f2 <o f1" := (ComV f2 f1) (at level 24, right associativity).

Variable tenV00 : forall V2 : obV, forall V1 : obV, obV.
Notation  "(0 V1 * V2 )0" := (tenV00 V2 V1) (at level 30, V1 at next level).
Check ( fun V2 V1 => (0 V1 *  V2 )0  ).
Variable tenV10 : forall V2 : obV, forall V1 V1' (v : arrV00 V1 V1'),  V(0 (0 V1* V2 )0 |- (0 V1' * V2 )0 )0.
Notation  "(1 v * V2 )0" := (tenV10 V2 v) (at level 30, v at next level).
Check ( fun V2 v => (1 v *  V2 )0  ).

Variable morV00 : obV -> obV -> obV.
Notation "[0 V1 ~> V2 ]0" := (morV00 V1 V2) (at level 30).
Variable morV01 : forall V1 : obV, forall V2 V2' (v : arrV00 V2 V2'), V(0 [0 V1 ~> V2 ]0 |- [0 V1 ~> V2' ]0 )0.
Notation "[0 V1 ~> v ]1" := (morV01 V1 v) (at level 30).
Variable morV10 : forall V1' V1 (v : arrV00 V1' V1), forall V2 : obV, V(0 [0 V1 ~> V2 ]0 |- [0 V1' ~> V2 ]0 )0.
Notation "[1 v ~> V2 ]0" := (morV10 v V2) (at level 30).

Variable Ten : forall V : obV, forall (U W : obV), V(0 U |- [0 V ~> W ]0 )0 -> V(0 (0 U * V )0  |- W )0.
Variable TenIn : forall V : obV, forall (U0 U1 W : obV), V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0 -> V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0.

Variable convV : forall V1 V2, V(0 V1 |- V2)0 -> V(0 V1 |- V2 )0 -> Prop.
Notation "v2 ~~ v1" := (convV v2 v1)  (at level 70).
Variable CongCom : forall A2 A3, forall (f2 f2' : V(0 A2 |- A3 )0), f2 ~~ f2' -> forall A1, forall (f1 f1' : V(0 A1 |- A2 )0), f1 ~~ f1' -> f2 <o f1 ~~ f2' <o f1'.
Variable ReflV : forall A1 A2 (f : V(0 A1 |- A2 )0), f ~~ f.
Variable TransV : forall A1 A2, forall (uModTrans f : V(0 A1 |- A2)0), uModTrans ~~ f -> forall (f' : V(0 A1 |- A2)0), f' ~~ uModTrans -> f' ~~ f.
Variable SymV : forall A1 A2,  forall (f' f : V(0 A1 |- A2)0), f ~~ f' -> f' ~~ f.
Variable Cat1RightV : forall A1 A2, forall f : V(0 A1 |- A2)0,  f ~~ f <o 1.
Variable Cat1LeftV : forall A1 A2, forall f : V(0 A1 |- A2)0,  f ~~ 1 <o f.
Variable Cat2V : forall A3 A4 (f3 : V(0 A3 |- A4)0), forall A2 (f2 : V(0 A2 |- A3)0), forall A1 (f1 : V(0 A1 |- A2)0),
                   (f3 <o f2) <o f1 ~~ f3 <o (f2 <o f1).

Variable obF : Type.
Variable polyF00 : obF -> obF -> obV.
Notation "F[0 A1 ~> A2 ]0" := (polyF00 A1 A2) (at level 30).

Parameter polyF : forall (B : obF), forall (V : obV) (A : obF),
                    V(0 V |- F[0 B ~> A ]0 )0 ->
                    forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0.

Notation "F[1 f ~> X ]0" := (@polyF _ _ _ f X) (at level 30).
Notation "F[0 X ~> g ]1" := (@polyF _ _ _ 1 X <o g) (at level 30).
Notation "F[0 B ~> - ]1" := (fun A X => @polyF _ _ _ (@IdenV (F[0 B ~> A ]0)) X) (at level 30). 

Variable polyV : forall (W : obV), forall (U : obV) (V : obV),
                   V(0 U |- [0 W ~> V ]0 )0 ->
                   forall X : obV, V(0 [0 V ~> X ]0  |- [0 U ~> [0 W ~> X ]0 ]0 )0.

Notation "V[1 v ~> X ]0" := (@polyV _ _ _ v X) (at level 30).
Notation "V[0 X ~> w ]1" := (@polyV _ _ _ 1 X <o w) (at level 30).
Notation "V[0 W ~> - ]1" := (fun V X => @polyV _ _ _ (@IdenV ([0 W ~> V ]0)) X) (at level 30). 

Variable polyV_monoV : forall (W : obV), forall (U : obV) (V : obV),
                       forall (v : V(0 U |- [0 W ~> V ]0 )0), forall X : obV,
                         TenIn( V[1 v ~> X ]0 )
                              ~~ [1 Ten v ~> X]0 .

Variable polyF_arrow :  forall (B : obF) (A : obF) (V : obV),
                        forall (V' : obV) (v : V(0 V' |- V )0),
                        forall (f : V(0 V |- F[0 B ~> A ]0 )0) (X : obF),
                          F[1 f <o v ~> X ]0
                           ~~ [1 v ~> F[0 B ~> X ]0 ]0 <o F[1 f ~> X ]0 .

Variable polyF_morphism :  forall (B : obF) (A : obF) (V : obV),
                           forall (W : obV) (A' : obF) (g : V(0 W |- F[0 A ~> A']0 )0),
                           forall (f : V(0 V |-F[0 B ~> A ]0 )0) (X : obF),
                             F[1 Ten( [1 f ~> F[0 B ~> A' ]0 ]0 <o F[0 A' ~> g ]1 ) ~> X]0
                              ~~  TenIn( [0 W ~> F[1 f ~> X ]0 ]1 <o F[1 g ~> X ]0 ).

Lemma polyF_natural : forall (B : obF) (V : obV) (A : obF) (f : V(0 V |- F[0 B ~> A ]0)0),
                      forall (C X : obF),
                        ( [0 F[0 A ~> C ]0 ~> F[1 f ~> X ]0 ]1 <o F[0 A ~> - ]1 C X )
                          ~~ ( [1 F[1 f ~> C ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0 <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) .

  