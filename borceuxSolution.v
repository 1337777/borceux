(*+ borceuxSolution.v +*)

(******************************************

Proph

https://github.com/1337777/borceux/blob/master/borceuxSolution.v

1. Short: This [1] solves some question of Ahrens [2] and Kan-Riehl [3], which is how to program Kelly's <<enriched categories>> and how the inter-dependence of <<naturality>> with <<category>> is cyclic. Also This [4] attempts to clarify the contrast <<categorical algebra>> (ring/locale-presentation and its "internal logic"), from <<categorial logic>> in the style of the <<enriched/encoded/programmed/recursion>> categories of Kelly-Dosen or Lawvere-Lambek and as attempted in [5], for example : the yoneda lemma and most categorial lemmas are no-more-than Gentzen's constructive logic of re-arranging the input-output positions <<modulo naturality>>. Now homotopy/knots/proof-nets may be held as (faithfull or almost-faithfull) semantical techniques (<<descent>>) to do this <<categorial logic>>, and the homotopy itself may be programmed in specialized grammars (for example [6] or HOTT).

2. The common assumption that catC( - , X ) is dual to catC( Y , - ) is FALSIFIED. This falsification originates from the description of the composition as some binary form instead of as some functional form which is programmed/encoded/enriched onto the computer. Then get some new thing which is named <<polymorphism>> from which to define <<polymorph category>>. This is the only-ever real description and deduction of the yoneda lemma, which says that the image of polyF (which is injective and contained in natural transformations) also contains all natural transformations.

3. Some polymorph category is given by polyF, which is commonly ( _1 o> _2 ), polymorph in V and polymorph in A :
Variable obF : Type.
Variable polyF00 : obF -> obF -> obV.
Notation "F[0 A1 ~> A2 ]0" := (polyF00 A1 A2) (at level 25).
Parameter polyF : forall (B : obF), forall (V : obV) (A : obF),
                    V(0 V |- F[0 B ~> A ]0 )0 ->
                    forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0.

4. And to get polymorph functor, instead of describing F : catA --> catB  then (contrast yoneda structures) describe catV[ V , catB[ B , F - ] ] : catA --> catV
   And to get polymorph transformation, instead of describing phi A : G A -> H A  then a-la-dosen (contrast weighted colimiting Kan extension) describe phi _f : catV( V , catB[ B , G A ] ) ->  catV( V , catB[ B , H A ] )

5. Stake for nondependent Solution Programme Seminary at FMCS2016 and ICMS2016 :
paypal 1337777.OOO@gmail.com , wechatpay 2796386464 , irc #OOO1337777

[1] 1337777.OOO, https://github.com/1337777/borceux/blob/master/borceuxSolution.v
[2] Ahrens, https://github.com/benediktahrens/monads/blob/trunk/CAT/enriched_cat.v
[3] Riehl, http://www.math.jhu.edu/~eriehl/context.pdf
[4] 1337777.OOO, https://github.com/1337777/borceux/blob/master/chic05.pdf
[5] 1337777.OOO, https://github.com/1337777/dosen/blob/master/itp.pdf
[6] Ye, http://katherineye.com/post/129960474471/strange-loops-capturing-knots-with-powerful

* use this authorizing-geolocated-timed-tutoring tool to play these links as TV !
http://1337777.link/ooo/guJAHkwRZYYyuhrh4GyYWv7BPOwNEF-jSeQcYN9WxLk!Zw1GYSFfr6cheRhkPhTPCnsog7DFPZQUCcv7ZEKh22s

******************************************)

Set Implicit Arguments.

(** ** put any category V **)

Variable obV : Type.
Variable arrV00 : obV -> obV -> Type.
Notation "V(0 V1 |- V2 )0" := (arrV00 V1 V2) (at level 35).

Variable IdenV : forall {V : obV}, V(0 V |- V )0.
Notation "1" := (@IdenV _) (at level 0).

Variable ComV : forall UCom V3, V(0 UCom |- V3 )0 -> forall V1, V(0 V1 |-  UCom )0 -> V(0 V1 |- V3 )0.
Notation "f2 <o f1" := (ComV f2 f1) (at level 33, right associativity).
Notation "f1 o> f2" := (ComV f2 f1) (at level 34, right (*yes right*) associativity).

Variable convV : forall V1 V2, V(0 V1 |- V2)0 -> V(0 V1 |- V2 )0 -> Prop.
Notation "v2 ~~ v1" := (convV v2 v1)  (at level 70).

Hypothesis CongCom : forall A2 A3, forall (f2 f2' : V(0 A2 |- A3 )0), f2 ~~ f2' -> forall A1, forall (f1 f1' : V(0 A1 |- A2 )0), f1 ~~ f1' -> f2 <o f1 ~~ f2' <o f1'.
Hypothesis ReflV : forall A1 A2 (f : V(0 A1 |- A2 )0), f ~~ f.
Hypothesis TransV : forall A1 A2, forall (uTrans f : V(0 A1 |- A2)0), uTrans ~~ f -> forall (f' : V(0 A1 |- A2)0), f' ~~ uTrans -> f' ~~ f.
Hypothesis SymV : forall A1 A2,  forall (f' f : V(0 A1 |- A2)0), f ~~ f' -> f' ~~ f.
Hypothesis Cat1RightV : forall A1 A2, forall f : V(0 A1 |- A2)0,  f ~~ f <o 1.
Hypothesis Cat1LeftV : forall A1 A2, forall f : V(0 A1 |- A2)0,  f ~~ 1 <o f.
Hypothesis Cat2V : forall A3 A4 (f3 : V(0 A3 |- A4)0), forall A2 (f2 : V(0 A2 |- A3)0), forall A1 (f1 : V(0 A1 |- A2)0),
                     (f3 <o f2) <o f1 ~~ f3 <o (f2 <o f1).


(** ** put functional monoidal logic onto V **)

Variable desV00 : forall V2 : obV, forall V1 : obV, obV.
Notation  "(0 V1 * V2 )0" := (desV00 V2 V1) (at level 30, V1 at next level).
Check ( fun V2 V1 => (0 V1 *  V2 )0  ).
Variable desV10 : forall V2 : obV, forall V1 V1' (v : arrV00 V1 V1'),  V(0 (0 V1* V2 )0 |- (0 V1' * V2 )0 )0.
Notation  "(1 v * V2 )0" := (desV10 V2 v) (at level 30, v at next level).
Check ( fun V2 v => (1 v *  V2 )0  ).

Variable consV00 : obV -> obV -> obV.
Notation "[0 V1 ~> V2 ]0" := (consV00 V1 V2) (at level 30).
Variable consV01 : forall V1 : obV, forall V2 V2' (v : arrV00 V2 V2'), V(0 [0 V1 ~> V2 ]0 |- [0 V1 ~> V2' ]0 )0.
Notation "[0 V1 ~> v ]1" := (consV01 V1 v) (at level 30).
Variable consV10 : forall V1' V1 (v : arrV00 V1' V1), forall V2 : obV, V(0 [0 V1 ~> V2 ]0 |- [0 V1' ~> V2 ]0 )0.
Notation "[1 v ~> V2 ]0" := (consV10 v V2) (at level 30).

Variable Des : forall V : obV, forall (U W : obV), V(0 U |- [0 V ~> W ]0 )0 -> V(0 (0 U * V )0  |- W )0.
Hypothesis CongDes : forall V : obV, forall (U W : obV), forall (f f' : V(0 U |- [0 V ~> W ]0 )0),
                     f' ~~ f -> Des f' ~~ Des f.
Variable DesIn : forall V : obV, forall (U0 U1 W : obV), V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0 -> V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0.
Variable CongDesIn : forall V : obV, forall (U0 U1 W : obV), forall (v v' : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0),
                       v' ~~ v -> DesIn v' ~~ DesIn v.
Variable ConsIn : forall V : obV, forall (U0 U1 W : obV), V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0 -> V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0.
Hypothesis CongConsIn : forall V : obV, forall (U0 U1 W : obV), forall (v v' : V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0),
                         v' ~~ v -> ConsIn v' ~~ ConsIn v.
Hypothesis ConsIn_DesIn : forall V : obV, forall (U0 U1 W : obV), forall (f : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0),
                           ConsIn (DesIn f) ~~ f.
Hypothesis DesIn_Input : forall V : obV, forall (U0 U1 W : obV), forall (v : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0), forall (U0' : obV) (i : V(0 U0' |- U0 )0),
                     (DesIn v) <o i ~~ DesIn( v <o i ).


(** ** get the definition of polymorph category F **)

Variable obF : Type.
Variable polyF00 : obF -> obF -> obV.
Notation "F[0 A1 ~> A2 ]0" := (polyF00 A1 A2) (at level 25).

Parameter polyF : forall (B : obF), forall (V : obV) (A : obF),
                    V(0 V |- F[0 B ~> A ]0 )0 ->
                    forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0.

(* therefore "F[1 f ~> X ]0" is similar to ( f o> _ ) *)
Notation "F[1 f ~> X ]0" := (@polyF _ _ _ f X) (at level 25).

(* therefore "F[0 X ~> g ]1" is similar to the common ( _ <o g ) *)
Notation "F[0 X ~> g ]1" := (@polyF _ _ _ (@IdenV _) X <o (g : V(0 _ |- F[0 _ ~> X ]0 )0)) (at level 25).


(** related to correspondence with the common representation **)
Variable polyF_arrow :  forall (B : obF) (A : obF) (V : obV),
                        forall (V' : obV) (v : V(0 V' |- V )0),
                        forall (f : V(0 V |- F[0 B ~> A ]0 )0) (X : obF),
                          F[1 f <o v ~> X ]0
                           ~~ [1 v ~> F[0 B ~> X ]0 ]0 <o F[1 f ~> X ]0 .

(** related to associativity, polyF_morphism says that, put the parameter f and the modifier argument g, then get
        (outer modification)    ( g <o f ) o> _  =  f o> ( g o> _ )    (inner modification)
which is, holding only f as parameter and running all the arguments,
        (outer modification)    ( _1 <o f ) o> _2  =  f o> ( _1 o> _2 )    (inner modification)
 **)
Variable polyF_morphism :  forall (B : obF) (A : obF) (V : obV),
                           forall (W : obV) (A' : obF) (g : V(0 W |- F[0 A ~> A']0 )0),
                           forall (f : V(0 V |-F[0 B ~> A ]0 )0) (X : obF),
                             F[1 Des( [1 f ~> F[0 B ~> A' ]0 ]0 <o F[0 A' ~> g ]1 ) ~> X]0
                              ~~  DesIn( [0 W ~> F[1 f ~> X ]0 ]1 <o F[1 g ~> X ]0 ).

Hypothesis CongPolyF : forall (B : obF), forall (V : obV) (A : obF),
                       forall (f f' : V(0 V |- F[0 B ~> A ]0 )0),
                         f' ~~ f -> forall X : obF, polyF f' X ~~ polyF f X.

Definition polyF_IdenV : forall (B : obF), forall (A : obF),
                         forall X : obF, V(0 F[0 A ~> X ]0  |- [0 F[0 B ~> A ]0 ~> F[0 B ~> X ]0 ]0 )0
  := (fun B A X => @polyF B (F[0 B ~> A ]0) A (@IdenV (F[0 B ~> A ]0)) X).
Notation "F[0 B ~> - ]1" := (@polyF_IdenV B) (at level 25).


(** ** get that the logical category V is polymorph **)

Variable polyV : forall (W : obV), forall (U : obV) (V : obV),
                   V(0 U |- [0 W ~> V ]0 )0 ->
                   forall X : obV, V(0 [0 V ~> X ]0  |- [0 U ~> [0 W ~> X ]0 ]0 )0.

Notation "V[0 U ~> V ]0" := ([0 U ~> V ]0) (at level 25, only parsing).
Notation "V[1 v ~> X ]0" := (@polyV _ _ _ v X) (at level 25).
Notation "V[0 X ~> w ]1" := (@polyV _ _ _ 1 X <o w) (at level 25).
Notation "V[0 W ~> - ]1" := (fun V X => @polyV _ _ _ (@IdenV ([0 W ~> V ]0)) X) (at level 25). 

Hypothesis polyV_monoV : forall (W : obV), forall (U : obV) (V : obV),
                       forall (v : V(0 U |- [0 W ~> V ]0 )0), forall X : obV,
                         [1 Des v ~> X]0
                                       ~~ DesIn( V[1 v ~> X ]0 ) .

Hypothesis polyV_arrow :  forall (B : obV) (A : obV) (V : obV),
                        forall (V' : obV) (v : V(0 V' |- V )0),
                        forall (f : V(0 V |- V[0 B ~> A ]0 )0) (X : obV),
                          V[1 f <o v ~> X ]0
                           ~~ [1 v ~> V[0 B ~> X ]0 ]0 <o V[1 f ~> X ]0 .


(** ** get that the image of polyF are contained in natural transformations **)

Lemma polyF_arrowIn :  forall (B : obF) (A : obF) (V : obV),
                        forall (W V' : obV) (v : V(0 W |- [0 V' ~> V ]0 )0),
                        forall (f : V(0 V |- F[0 B ~> A ]0 )0) (X : obF),
                          F[1 f <o (Des v) ~> X ]0
                           ~~ DesIn( V[1 v ~> F[0 B ~> X ]0 ]0 <o F[1 f ~> X ]0 ) .
Proof.
  intros; eapply TransV; [ apply DesIn_Input | ].
  eapply TransV; [ | apply polyF_arrow ].
  eapply CongCom; [ | eapply ReflV]; apply polyV_monoV.
Qed.

(** polyF_natural (sym) says that, put the parameter f, then get
        (outer modification)    _1 <o ( f o> _2 )  =  f o> ( _1 <o _2 )    (inner modification)
and this is codeductible with polyF_morphism above which says that, put the parameter f, then get
        (outer modification)    ( _1 <o f ) o> _2  =  f o> ( _1 o> _2 )    (inner modification)
now memo that in the left hand sides there is mirroring of whole and permutation of inputs, and that in the right hand sides there is mirroring of block and permutation of inputs,
 **)
Lemma polyF_natural : forall (B : obF) (V : obV) (A : obF) (f : V(0 V |- F[0 B ~> A ]0)0),
                      forall (C X : obF),
                        ( [0 F[0 A ~> C ]0 ~> F[1 f ~> X ]0 ]1
                          <o F[0 A ~> - ]1 C X )
                          ~~ ( [1 F[1 f ~> C ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
                               <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) .
Proof.
  (* enough ( DesIn( _ ) ~~ DesIn( _ ) ) *)
  intros;  eapply TransV; [ eapply TransV | ]; [ apply ConsIn_DesIn | idtac | apply SymV, ConsIn_DesIn].
  apply CongConsIn.

  (* convert left hand side : outer polyF_morphism then inner polyF_arrow *)
  assert ( LHS1 : F[1 Des( [1 f ~> F[0 B ~> C ]0 ]0 <o F[0 C ~> (@IdenV (F[0 A ~> C]0)) ]1 ) ~> X ]0
                   ~~ DesIn( [0 F[0 A ~> C ]0 ~> F[1 f ~> X ]0 ]1 <o F[0 A ~> - ]1 C X ) )
    by apply polyF_morphism.

  assert ( LHS2 : F[1 Des( F[1 (@IdenV (F[0 B ~> A ]0)) <o f  ~> C ]0 ) ~> X ]0
                   ~~ F[1 Des( [1 f ~> F[0 B ~> C ]0 ]0 <o F[0 C ~> (@IdenV (F[0 A ~> C]0)) ]1 ) ~> X ]0 )
    by ( apply CongPolyF, CongDes;  eapply TransV; [ eapply Cat2V | ]; eapply TransV; [ eapply Cat1RightV | ];
         apply polyF_arrow ).

  (* convert left hand side : outer polyV_arrow then outer polyF_arrowIn which is inner form of polyF_arrow *)
  assert ( RHS1 : DesIn( ( V[1 (@IdenV (V[0 V ~> (F[0 B ~> C ]0) ]0)) <o (F[1 f ~> C ]0) ~> (F[0 B ~> X ]0) ]0 ) <o F[0 B ~> - ]1 C X )
                       ~~ DesIn( [1 F[1 f ~> C ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0 <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) )
    by ( eapply TransV; [ eapply CongDesIn; eapply Cat2V | ];
         apply CongDesIn; apply CongCom; [ | apply ReflV];
         apply polyV_arrow ).

  assert ( RHS2 : ( F[1 (@IdenV (F[0 B ~> C ]0)) <o Des( (@IdenV (V[0 V ~> (F[0 B ~> C ]0) ]0)) <o (F[1 f ~> C ]0) ) ~> X ]0 )
                    ~~ DesIn( ( V[1 (@IdenV (V[0 V ~> (F[0 B ~> C ]0) ]0)) <o (F[1 f ~> C ]0) ~> (F[0 B ~> X ]0) ]0 ) <o F[0 B ~> - ]1 C X ) )
    by apply polyF_arrowIn.

  (* clean right hand side *)
  eapply TransV; [ apply RHS1 | ] .  eapply TransV; [ apply RHS2 | ]. clear RHS2 RHS1.
  eapply TransV; [ apply CongPolyF, Cat1LeftV | ]. eapply TransV; [ apply CongPolyF, CongDes, Cat1LeftV | ].

  (* clean left hand side *)
  eapply TransV; [ | apply SymV, LHS1 ] .  eapply TransV; [ | apply SymV, LHS2 ]. clear LHS2 LHS1.
  eapply TransV; [ | apply CongPolyF, CongDes, CongPolyF, SymV, Cat1LeftV ].
  
  apply ReflV.
Qed.


(** ** get that the image of polyF contains all natural transformations **)

Variable IdenObV : obV.
Notation  "'I'" := (IdenObV) (at level 0).

Parameter unitF : forall {A : obF}, V(0 I |- F[0 A ~> A ]0 )0.
Notation "'u'" := (@unitF _) (at level 0).

Variable DesIdenObR : forall (U W : obV), V(0 U |- [0 I ~> W ]0 )0 -> V(0 U  |- W )0.
Hypothesis CongDesIdenObR : forall (U W : obV), forall (v v' : V(0 U |- [0 I ~> W ]0 )0),
                              v' ~~ v -> DesIdenObR v' ~~ DesIdenObR v.
Hypothesis DesIdenObR_output : forall (U : obV) (W W' : obV) (w : V(0 W |- W' )0), forall v : V(0 U |- [0 I ~> W ]0 )0, 
                                 DesIdenObR( [0 I ~> w ]1 <o v ) ~~ w <o DesIdenObR( v ).

Variable DesIdenObL : forall V : obV, forall (W : obV), V(0 I |- [0 V ~> W ]0 )0 -> V(0 V |- W )0.
Variable ConsIdenObL : forall V : obV, forall (W : obV), V(0 V |- W )0 -> V(0 I |- [0 V ~> W ]0 )0.
Hypothesis ConsIdenObL_DesIdenObL : forall V : obV, forall (W : obV), forall v : V(0 I |- [0 V ~> W ]0 )0,
                                       v ~~ ConsIdenObL( DesIdenObL v).
Hypothesis CongConsIdenObL : forall V : obV, forall (W : obV), forall (v v' : V(0 V |- W )0),
                                v' ~~ v -> ConsIdenObL v' ~~ ConsIdenObL v.

Hypothesis consV10_functorial : forall V1' V1 (v : arrV00 V1' V1), forall V1'' (v' : arrV00 V1'' V1'), forall V2 : obV,
                                 [1 v <o v' ~> V2 ]0 ~~  [1 v' ~> V2 ]0 <o  [1 v ~> V2 ]0 .
Hypothesis consV11_bifunctorial : forall V1' V1 (v : arrV00 V1' V1), forall W1 W1' (w : arrV00 W1 W1'),
                                   [0 V1' ~> w ]1 <o  [1 v ~> W1 ]0 ~~ [1 v ~> W1' ]0 <o [0 V1 ~> w ]1 .
Hypothesis CongConsV10 : forall V1' V1 (v v' : arrV00 V1' V1), forall V2 : obV,
                          v' ~~ v -> [1 v' ~> V2 ]0 ~~ [1 v ~> V2 ]0 .

(** related to non-variance when unit pull the input **)
Hypothesis polyF_unitF : forall (A : obF), forall X : obF, (@IdenV (F[0 A ~> X ]0)) ~~ DesIdenObR( F[1 (@unitF A) ~> X ]0 ) .

(** related to non-variance when unit push the output,
       therefore polyF is injective **)
Hypothesis polyF_inputUnitF : forall (B : obF), forall (V : obV) (A : obF),
                              forall (f : V(0 V |- F[0 B ~> A ]0 )0),
                                f  ~~ DesIdenObL( (F[1 f ~> A ]0) <o (@unitF A) ).

Definition natural (B : obF) (V : obV) (A : obF) (φ : forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0 ) :=
  forall (C X : obF),
    ( [0 F[0 A ~> C ]0 ~> φ X ]1
      <o F[0 A ~> - ]1 C X )
      ~~ ( [1 φ C ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
           <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) .

Lemma natural_unitF_explicit : forall (B : obF) (V : obV) (A : obF) (φ : forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0 ),
                                 natural φ ->
                                 forall (X : obF),
                                   DesIdenObR( [1 φ A <o (@unitF A) ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
                                               <o ( V[0 V ~> - ]1 (F[0 B ~> A ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 A X )
                                             ~~ ( φ X ) .
Proof.
  intros; eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ | apply ReflV]; apply consV10_functorial ].
  eapply TransV; [ | eapply CongDesIdenObR; eapply Cat2V ].
  eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ apply ReflV | ]; apply SymV, H ].
  eapply TransV; [ | eapply CongDesIdenObR; eapply SymV, Cat2V ].
  eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ | apply ReflV ]; apply SymV, consV11_bifunctorial ].
  eapply TransV; [ | eapply CongDesIdenObR; eapply Cat2V ].
  eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ apply ReflV | ]; apply SymV, polyF_arrow ].
  eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ apply ReflV | ]; apply CongPolyF, SymV, Cat1LeftV ].  
  eapply TransV; [ | eapply DesIdenObR_output].
  eapply TransV; [ | eapply CongCom; [ apply ReflV | ]; apply SymV, polyF_unitF ].
  apply SymV, Cat1RightV.
Qed.

Lemma natural_unitF : forall (B : obF) (V : obV) (A : obF) (φ φ' : forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0 ),
                        natural φ -> natural φ' ->
                        φ' A <o (@unitF A)  ~~ φ A <o (@unitF A) ->
                        forall X : obF, φ' X ~~ φ X.
Proof.
  intros; eapply TransV; [ apply natural_unitF_explicit; assumption |
                          eapply TransV; [ | apply SymV, natural_unitF_explicit; assumption ] ].
  apply CongDesIdenObR, CongCom; [ | apply ReflV ]; apply CongConsV10.
  assumption.
Qed.

Lemma YONEDA : forall (B : obF) (V : obV) (A : obF) (φ : forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0 ),
                 natural φ ->
                 forall X : obF, φ X ~~ F[1 DesIdenObL( (φ A) <o (@unitF A) ) ~> X ]0.
Proof.
  intros; enough( φ A <o (@unitF A) ~~ F[1 DesIdenObL( (φ A) <o (@unitF A) ) ~> A ]0 <o (@unitF A) ).
  apply natural_unitF; [ |  assumption | assumption ] .
  unfold natural; intros; apply polyF_natural.
  
  eapply TransV; [ apply SymV, ConsIdenObL_DesIdenObL | ].
  eapply TransV; [ | apply ConsIdenObL_DesIdenObL].
  apply CongConsIdenObL.
  eapply TransV; [ apply polyF_inputUnitF |  apply ReflV ].
Qed.


Module Functor.
  (** ** next : polymorph functor **)
  (** instead of describing F : catA --> catB  then (contrast yoneda structures) describe catV( V , catB[ B , F - ] ) : catA --> catV **)
End Functor.


Module Transformation.
  (** ** next : polymorph transformation **)
  (** instead of describing φ A : G A -> H A  then a-la-dosen (contrast weighted colimiting Kan extension) describe φ _f : catV( V , catB[ B , G A ] ) ->  catV( V , catB[ B , H A ] ) **)
End Transformation.
