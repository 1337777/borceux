(*+ borceuxSolution.v +*)

(**_____________________________________________________________________________

Proph,

archive.org  https://github.com/1337777/borceux/blob/master/borceuxSolution2.v

1. is successor of some earlier text which describes how to program <<polymorphism>> ("enriched categories"). The finding is that some functor or category (identity functor) is given by the data

polyF : forall (log : logic) (dat : data log) (V : obV log) (B : obB dat) (A : obA dat),
log.-V(0 V |- dat.-F[0 B ~> A ]0 )0 ->
forall X : obA dat, log.-V(0 dat.-A[0 A ~> X ]0 |- log.-[0 V ~> dat.-F[0 B ~> X ]0 ]0 )0 

, where dat.-F[0 B ~> A ]0  denotes  dat.-B[0 B ~> dat.-F|0 A ]0 , which is polymorph in V and polymorph in A . And the Coq meta logic and the functors logic and the yoneda lemma are now described fully only within this new polymorphism phrasing.

2. TL;DR: Following [1], this may be described by the notation ( ( _1 _3 ) o>F _2 ) which is not reality, and polymorph/commuting/natural/associativity in A says
( ((b _v) o>F (a _w)) o>F a' )   ~~   ( (b _v) o>F ((a _w) o>A a') )

3. This solution may be viewed as continuing the programme of Gentzen natural (=polymorphic) deduction and Dosen cut elimination for adjunctions, where Dosen critically did replace the counit by the primitive ( counit o> _ ) .
    Therefore this solution also shows <<cut elimination/desintegration for these polymorph functors/categories>> and eventually for polymorph adjunctions and polymorph monads . 

4. And that any category is some identity functor is precisely mirrored in the <<data-class interfaces>>  and the <<sharings constraints>> and the <<automatic declassifications>>  ("packaging  interfaces and their inheritance coercions", "structure vs property") .

5. And this new polymorphism thing is better for the  <<semi-programmed semi-automatic classification of data>> ("canonical structures", "garbage collector") . Also remember that the purely-logical non-polymorphism parts of in the deductions are automatically solved by some small-scale reflection into the decision-dissolvers enabled by the Dosen cut elimination in adjunctions technique and the Maclane associativity coherence technique and any other coherence technique.

6. One question which is lacking is to describe  how any functor's polymorphism is actually some (more common) polymorphism of some metatransformation inside the Coq meta logic. This question is related to the question of how to really define functor and composition of functors.
    QUESTION:

7. Another question is how to get some alternative presentation of the logic which is mostly functional instead of being in the common monoidal form.

8. tutoring mathcomp mathcomp overview main techniques [2] [3] [4] including notations and canonical structures

    , new programme of 133777.ooo reviews  and com following functional alternative instead of monoidal  of Dosen coherence books involves combinatorics geometry and numbers.

9. ct2016 friday question and announce programme ,  paypal wechatpay irc,  1337777.ooo/links

[1] ฅ( ̳• ◡ • ̳)ฅ-Ye ,  https://github.com/hypotext/notation
[2] mathcomp1
[3] mathcomp2
[4] mathcomp3


__USER MANUAL__

__notation for polyF

(f _v) o>F g    ... f logical-indexing in the codomain ... g change of morphism-index in the domain

__polymorph in B says

b : log.-V(0 W |- dat.-B[0 B' ~> B ]0 )0

 ... ( (f _v) <o b ) o>F g   ~~  ( (f _v) o>F g ) <o b

( (b _w) o>B (f _v) ) o>F g   ~~  (b _w) o>B ( (f _v) o>F g )

____ and particular when f is unitB constance and polyB_inputUnitB present

(b _w) o>B ( unitB o>F g ) ~~ ( (b _w) o>B unitB ) o>F g
                           ~~ (b _w) o>F g

then get B[B ~> -] <o F|1 A X ~~ F[B ~> -] A X

__polymorph in V says

((f <<o v) _v')) o>F g  ~~  (f (v _v')) o>F g   /!\ argument _v' is inputed only later /!\

__polymorph in A says

((f _v) o>F (a _w)) o>F g ~~  (f _v) o>F ((a _w) o>A g)

__composition of functors says

(f' _w) o>F' ( (f _v) o>F g )

++ (f' _w) o>F'Fnew ( (f _v) ; g ) assuming some associativity axiom(s), then can do the generality above by only right inputing into F and left-right-inputing into F':
(f' _w) o>F' ( (f _v) o>F g )  ~~ (f' _w) o>F' ( (f _v) o>B (1 o>F g) ) 
( (f' _w) o>F' (f _v) ) o>F' (1 o>F g)
= ( (f' _w) o>F' (f _v) ) o>F'Fold g


++ now yoneda does not require this extra associativity axiom(s), therefore may be some new notion of functor or composition of functor


__functor unit
(f _v) o>F 1 ~~ (f _v)

__form unit
1 o>A g ~~ g

__cut desintegration , memo that polymorphisms in V is not really useful

+ functor o>F cut desintegration
(f _v) o>F g

++ (f _v) o>F 1  ~~  (f _v)  ... o>F not linked

++ (f _v) o>F (g'' o>A g')  ~~  ((f _v) o>F g'') o>A g'  ... o>F linked to o>F

++ g generative

+++ 1 o>F ggen  ... atomic

+++ ((f _v) o>F g') o>F ggen  ~~ (f _v) o>F (g o>A ggen)  ...  o>F linked to o>A

+++ (fgen _v) o>F ggen  ... atomic

+ category o>A cut desintegration
g1 o>A g2  ... cut desintegration of o>F only now, if want cut desintegration of o>A then require more properties on catA than polyA_unitA, for example polyA_morphism

++ g1 o>A 1   ???

++ g1 o>A (g2'' o>A g2')  ???

++ g2 generative

+++ 1 o>A g2gen  ~~ g2gen   ... atomic

+++ (g1' o>A g1'') o>A g2gen  ???

+++ g1gen o>A g2gen  ... atomic

_____________________________________________________________________________**)

Module METALOGIC.
  Global Set Universe Polymorphism.
  Global Set Implicit Arguments.
  Global Unset Strict Implicit.
  Global Unset Printing Implicit Defensive.
  
  (** ultimate meta logic (Coq type theory) T , which enrich all the subject logics instances of the interface V ... 

now T is on top of Type is instance of meta/logical category with interface V , 
++    any instance of interface V is enriched in T , 
++   T is both ordinary (in T) and enriched in itself T where ordinary (0 _ |- _ )0 coincide with enriched [0 _  ~> _ ]0  ,
++    TODO NEXT: show polymorphicity (polyF_morphism or polyF_arrow) of category or functor  is naturality (metaα_morphism or metaυ_morphism) of meta transformation polyF (in index A or index V) where the logic is the T instance of interface V; Also is it necessary, for efficient semi-automatic semi-programmed canonical resolution/synthesis of the polymorphicity class,  that one shall express polymorphicity as naturality in the ultimate Coq meta logic T ? Or is polymorphicity-as-is workable ?

later, top interface is  polyfunctor, get category by putting F is identity : obA -> obB := obA   and now polyF_morphism becomes the wanted polyA_morphism ,   get metafunctor by putting  obB := obV   and now polyF_morphism becomes the wanted metaF_morphism  **)

  Definition obT : Type := Type. 
  Definition polyT_relT00 : obT -> obT -> obT := fun T1 T2 => T1 -> T2.
  Notation "T(0 B |- A )0" := (polyT_relT00 B A) (at level 35, format "T(0  B  |-  A  )0").

  (** TODO: how to define conversion such to avoid functional extensionality for T ?
comprehended as conversion on the enriched data **)
  (*Inductive convT : forall T1 T2, T(0 T1 |- T2)0 -> T(0 T1 |- T2 )0 -> Prop :=
  convT_Base : forall T1 T2 f g,  (forall t1, f t1 = g t1) -> @convT T1 T2 f g
| convT_Step : forall T1 T21 T22 f g,  (forall t1 ,  (@convT T21 T22 (f t1) (g t1))) -> @convT T1 (T21 -> T22) f g.
   *)
  Definition convT : forall T1 T2, T(0 T1 |- T2)0 -> T(0 T1 |- T2 )0 -> Prop := fun T1 T2 => eq . (*forall t1, f t1 = g t1.*)
  Notation "v2 ~~T v1" := (convT v2 v1)  (at level 70).

  Definition polyT_relT : forall (T : obT), forall (B : obT), forall (A : obT),
                            ( T -> T(0 B |- A )0 ) ->
                            forall X : obT, T(0 A |- X )0  ->  ( T -> T(0 B |- X )0 )
    := (fun (T : obT) (B : obT)  (A : obT) (f : T -> T(0 B |- A )0) 
          (X : obT) (g : T(0 A |- X )0) (t : T) (b : B) =>   g (f t b)) .
  (*Arguments polyT_relT : simpl never.*)

  Definition cstT : forall {T2 : Type}, T2 -> forall {T1 : Type}, T1 -> T2 := fun T2 (t2 : T2) => fun T1 (_ : T1) => t2.
  (*Arguments cstT : simpl never.*)

  (** almost same as the common constant .. but no unit-picking mentionned **)
  Definition polyT_relT_constant : forall (B : obT), forall (A : obT),
                                     T(0 B |- A )0 -> forall X : obT, T(0 A |- X )0  -> T(0 B |- X )0
    := (fun (B A : obT) (f : T(0 B |- A )0) (X : obT) (g : T(0 A |- X )0) =>
          polyT_relT (cstT f) g tt) .
  (*Arguments polyT_relT_constant : simpl never.*)

  Definition idT {T : Type} : T -> T := fun x : T => x .
  Arguments idT : simpl never.

  Definition polyT_relT_identitary : forall (B : obT), forall (A : obT),
                                     forall X : obT, T(0 A |- X )0  -> T(0 B |- A )0 -> T(0 B |- X )0
    :=  fun (B : obT) => fun (A : obT) =>
                        fun X : obT =>  fun (a : T(0 A |- X )0) => fun (b : T(0 B |- A )0) =>
                                                              @polyT_relT (T(0 B |- A )0) B A idT X a b .
  (*Arguments polyT_relT_identitary : simpl never.*)

  Definition IdenT {T : obT} : T(0 T |- T )0 := @idT T .
  Notation "'1T" := (@IdenT _) (at level 0).

  Notation "T(1 b |- X )0" := (@polyT_relT _ _ _ b X) (at level 35, format "T(1  b  |-  X  )0").

  Notation "T(1I b |- X )0" := (@polyT_relT_constant _ _ b X) (at level 35, format "T(1I  b  |-  X  )0").
  Notation "b o>> a" := (@polyT_relT_constant _ _ b _ a) (at level 33, right associativity).
  Eval compute in  fun b a => b o>> a .

  Notation "T(0 X |- - )1" := (@polyT_relT_identitary _ _ X) (at level 35, format "T(0  X  |-  -  )1").
  Notation "T(0 X |- a )1" := (@polyT_relT_identitary _ _ X a) (at level 35, format "T(0  X  |-  a  )1").
  Notation "a <<o b" := (@polyT_relT_identitary _ _ _ a b) (at level 33, right associativity).
  Eval compute in  fun b a => a <<o b .

  Definition consT00 : obT -> obT -> obT.
    intros V1 V2. exact ( (V1 -> V2) % type). Defined.
  Definition consT01 : forall {V1 : obT}, forall V2 V2', (polyT_relT00 V2 V2') -> (polyT_relT00 (consT00 V1 V2)  (consT00 V1 V2')).
    intros ? ? ? v2 v12.  exact (fun _v1 => v2 ( v12 _v1 ) ). Defined.
  (* (consT01In U v2) is    outgetting (consT01 v2),   ALT innerly/contextually in the contextU,  is action of (consT01 v2) *)
  Definition consT01In : forall U : obT, forall V1 : obT, forall V2 V2', (polyT_relT00 V2 V2') ->
                                                          (polyT_relT00 U (consT00 V1 V2)) ->  (polyT_relT00 U  (consT00 V1 V2'))  .
    intros ? ? ? ? v2.
    intros u'v1'v2. exact ( (consT01 v2) <<o u'v1'v2 ) || exact (fun __u =>  consT01 v2 (u'v1'v2 __u) ). Defined.
  Check ( fun U : obT =>  fun V1 : obT => fun V2 V2' => fun v2 : (polyT_relT00 V2 V2') =>
                                                 fun u'v1'v2 : (polyT_relT00 U (consT00 V1 V2)) => fun __u =>
                                                                                                  fun _v1 => eq_refl :  ( (consT01In v2 u'v1'v2 __u) _v1 = (v2 <<o (u'v1'v2 __u)) _v1 ) ) .
  Definition consT10 : forall V1' V1, (polyT_relT00 V1' V1) -> forall {V2 : obT}, (polyT_relT00 (consT00 V1 V2) (consT00 V1' V2)).
    intros ? ? v1 ? v12 .  exact (fun _v1' => v12 (v1 _v1') ). Defined.
  Definition consT10In : forall U : obT, forall V1' V1, (polyT_relT00 V1' V1) -> forall V2 : obT, (polyT_relT00 U (consT00 V1 V2)) ->  (polyT_relT00 U (consT00 V1' V2) ) .
    intros ? ? ? v1 ? .
    intros u'v1'v2. exact ( (consT10 v1) <<o u'v1'v2  ) || exact (fun __u => consT10 v1 (u'v1'v2 __u) ) . Defined.
  Check ( fun U : obT => fun V1' V1 => fun v1 : (polyT_relT00 V1' V1) => fun V2 : obT =>
                                                                  fun u'v1'v2 : (polyT_relT00 U (consT00 V1 V2)) => fun __u =>
                                                                                                                   fun _v1' => eq_refl : ( (consT10In v1 u'v1'v2 __u) _v1'  = (v1 o>> (u'v1'v2 __u)) _v1' ) ) .
  Definition desT00 : forall V2 : obT, forall V1 : obT, obT.
    intros ? ? . exact (prod V1 V2). Defined.
  Definition desT10 : forall V2 : obT, forall V1 V1', (polyT_relT00 V1 V1') -> (polyT_relT00 (desT00 V2 V1) (desT00 V2 V1')).
    intros ? ? ? v (_v1, _v2). exact (v _v1, _v2). Defined.
  Definition ConsT : forall V : obT, forall (U W : obT), (polyT_relT00 (desT00 V U) W) -> (polyT_relT00 U (consT00 V W)).
    intros ? ? ? uv'w. exact (fun _u => fun _v => uv'w (_u, _v) ). Defined. 
  Definition DesT: forall V : obT, forall (U W : obT), (polyT_relT00 U (consT00 V W)) -> (polyT_relT00 (desT00 V U) W) .
    intros ? ? ? u'v'w. exact (fun _u_v => let (_u, _v) := _u_v in u'v'w _u _v ). Defined.

  Definition IdenObT : obT.
    exact unit. Defined.
  Definition unitT : forall {A : obT}, (polyT_relT00 IdenObT (consT00 A A) ).
    intros ? ?. exact (fun a => a). Defined.

  Definition AssocT : forall {V W :obT }, forall {U: obT }, T(0 (desT00 (desT00 W V )  U ) |- (desT00 W ( (desT00 V  U))  ) )0.
    intros. intro. destruct X. destruct d. exact ((u,v ),w).
  Defined.

  Definition unitT_relT : forall {A : obT}, (polyT_relT00 IdenObT (polyT_relT00 A A) ) .
    intros. intro. eapply IdenT.
  Defined.
  Print Grammar pattern.
  Notation  "(0T V1 & V2 )0" := (desT00 V2 V1) (at level 30, format "(0T  V1  &  V2  )0").
  Notation  "(1T v & V2 )0" := (@desT10 V2 _ _ v) (at level 30, format "(1T  v  &  V2  )0").
  Notation "[0T V1 ~> V2 ]0" := (consT00 V1 V2) (at level 30, format "[0T  V1  ~>  V2  ]0").
  Notation "[0T V1 ~> v ]1" := (@consT01 V1 _ _ v) (at level 30, format "[0T  V1  ~>  v  ]1").
  Notation "[1T v ~> V2 ]0" := (@consT10 _ _ v V2) (at level 30, format "[1T  v  ~>  V2  ]0").
  Notation  "'IT'" := (IdenObT) (at level 0).
  Notation "'uT'" := (@unitT _) (at level 0).

  (**  for T, class properties of data **)
  Axiom  functional_extensionality_T : forall {A B : obT}, forall (f g : T(0 A |- B )0),  (forall x, f x = g x) -> f = g.

  Lemma ReflT : forall A1 A2 (f : T(0 A1 |- A2 )0), f ~~T f.
  Proof.
    reflexivity.
  Qed.

  Lemma SymT : forall A1 A2,  forall (f' f : T(0 A1 |- A2)0), f ~~T f' -> f' ~~T f.
  Proof.
    symmetry. assumption.
  Qed.

  Lemma TransT : forall A1 A2, forall (uTrans f : T(0 A1 |- A2)0), uTrans ~~T f -> forall (f' : T(0 A1 |- A2)0), f' ~~T uTrans -> f' ~~T f.
  Proof.
    intros; eapply eq_trans; eassumption.
  Qed.

  Lemma Cong_polyT_relT :   forall (V : obT) (B A : obT) (f f' : T(0 V |- T(0 B |- A )0 )0),
                              (forall _v : V, f' _v ~~T f _v) -> forall X : obT,  forall a1 a2, a1 ~~T a2 -> forall _v, T(1 f' |- X )0 a1 _v ~~T T(1 f |- X )0 a2 _v .
    intros. compute. rewrite H, H0. reflexivity.
  Qed.

  Lemma CongDesT : forall V : obT, forall (U W : obT), forall (f f' : T(0 U |- [0T V ~> W ]0 )0),
                     f' ~~T f -> DesT f' ~~T DesT f .
    intros ? ? ? ? ? H .
    simpl. rewrite H. reflexivity.
  Qed.

  Lemma Des_ConsT : forall V : obT, forall (U W : obT), forall (f : T(0 (0T U & V )0 |-  W )0),
                      DesT (ConsT f) ~~T f .
  Proof.
    intros. apply functional_extensionality_T. intros [ ]. reflexivity.
  Qed.

  Lemma Des_OutputT : forall V : obT , forall (U W : obT ), forall (v : T(0 U |- T(0 V |- W )0 )0), forall W' (w : T(0 W |- W' )0),
                        DesT( [0T V ~> w ]1 <<o v ) ~~T w <<o DesT( v ) .
  Proof.
    intros. apply functional_extensionality_T. intros [ ]. reflexivity.
  Qed.

  (* this is some form of functional extensionality *)
  Lemma CongConsT : forall V : obT, forall (U W : obT), forall (v v' : T(0 (0T U & V )0 |- W )0 ),
                      v' ~~T v -> ConsT v' ~~T ConsT v .
  Proof.
    intros. compute. rewrite H. reflexivity.
  Qed.
  Lemma Cons_DesT : forall V : obT, forall (U W : obT), forall (f : T(0 U |-  [0T V ~> W ]0 )0),
                      ConsT (DesT f) ~~T f .
    reflexivity.
  Qed.

  Lemma Cons_InputT : forall V : obT, forall (U U' : obT) (w : T(0 U' |- U )0), forall (W : obT) (v : T(0 (0T U & V )0 |- W )0),
                        ConsT(v <<o (1T w & V )0 )  ~~T ConsT( v ) <<o w .
    intros.  reflexivity.
  Qed.

  Lemma Assoc_RevT : forall{V W U : obT},
                       T(0 (0T (0T U & V )0 & W )0 |- (0T U & (0T V & W )0 )0 )0 .
    intros. intros [[u' v'] w']. exact (u', (v', w')).
  Defined.

  Lemma Assoc_Assoc_RevT : forall(V W U : obT),
                             '1T ~~T (Assoc_RevT <<o (@AssocT V W U)) .
    intros. apply functional_extensionality_T. intros [? []]. reflexivity.
  Qed.
  Lemma Assoc_Rev_AssocT : forall(V W U : obT),
                             '1T ~~T ((@AssocT V W U) <<o Assoc_RevT) .
    intros. apply functional_extensionality_T. intros [[] ?]. reflexivity.
  Qed.

  Definition DesInT : forall (V : obT), forall (U0 U1 W : obT), T(0 U0 |- [0T U1 ~> [0T V ~> W ]0 ]0 )0 -> T(0 U0 |- [0T (0T U1 & V )0 ~> W ]0 )0.
    intros. apply ConsT. eapply polyT_relT_identitary. Check @AssocT. 2: eapply (@AssocT _ _ _).  eapply DesT.
    eapply DesT. exact X.
  Defined.

  Definition DesIdenObRT : forall {U W : obT}, T(0 U |- [0T IT ~> W ]0 )0 -> T(0 U  |- W )0 .
    intros. intro. apply X. assumption. exact tt.
  Defined.

  Definition DesIdenObLT : forall {V W : obT}, T(0 IT |- [0T V ~> W ]0 )0 -> T(0 V  |- W )0 .
    intros. intro. apply X. exact tt. assumption.
  Defined.

  Lemma polyT_relT_constant_rel_identitary :  forall (B : obT) , forall (A : obT) ,
                                              forall X : obT , forall (a : T(0 A |- X )0),  forall (b : T(0 B |- A )0),
                                                @polyT_relT_constant B A b X a ~~T  a <<o b  . 
  Proof.
    reflexivity.
  Qed.

  Lemma polyT_relT_arrow : forall (B A : obT) (V V' : obT) (v : T(0 V' |- V )0)
                             (f : T(0 V |- T(0 B |- A )0 )0) (X : obT),
                           forall (a1 : T(0 A |- X )0), forall a2, a1 ~~T a2 -> forall (_v' : V'),
                                                                      (T(1 f <<o v |- X )0) a1 _v' ~~T
                                                                                           ([1T v ~> T(0 B |- X )0 ]0 <<o (T(1 f |- X )0)) a2 _v'.
  Proof.
    intros * H * . rewrite H. reflexivity.
  Qed.

  Lemma polyT_relT_arrow_simpl :  forall (B : obT), forall (A : obT),
                                  forall (T T' : obT) (b : T' -> T),
                                  forall (f : T -> T(0 B |- A )0 ) (X : obT),
                                  forall (a : T(0 A |- X )0), forall (ttt: T'),
                                    T(1 (fun v' => f (b v')) |- X )0 a ttt
                                     ~~T T(1 f |- X )0 a (b ttt) .
  Proof.
    reflexivity.
  Qed.

  Lemma  polyT_relT_morphism : forall (V : obT) (B A : obT) (W : obT) (A' : obT)
                                 (g : T(0 W |- T(0 A |- A' )0 )0)
                                 (f : T(0 V |- T(0 B |- idT A )0 )0) (X : obT), forall (a' : T(0 idT A' |- X )0) (_w_v : (0T W & V )0),
                                 T(1 DesT([1T f ~> T(0 B |- idT A' )0 ]0 <<o (T(1 '1T |- A' )0) <<o g) |- X )0 a' _w_v
                                  ~~T DesInT ([0T W ~> T(1 f |- X )0 ]1 <<o (T(1 g |- X )0)) a' _w_v.
  Proof.
    intros. destruct _w_v. reflexivity.
  Qed.
  
  (** written here :   (outer modification) ~~ (inner modification) **)
  Lemma polyT_relT_morphism_simpl :  forall (B : obT), 
                                     forall (A : obT) (A' : obT) (g : T(0 A |- A')0),
                                     forall (X : obT), forall (pull : T(0 B |- A)0), forall (push : T(0 A'  |- X )0 ),
                                       T(1I T(0 A' |- g )1 pull |- X )0 push
                                        ~~T  T(0 X |- T(1I g |- X )0 push )1 pull .
  Proof.
    reflexivity.
  Qed.

  (** related to non-variance when unit pull the input, commonly  ( 1 o> h ) ~~ h  **)
  Lemma polyT_relT_unitT : forall A X : obT, forall a1 a2, a1 ~~T a2 ->
                                                 @IdenT _ a1 ~~T DesIdenObRT (T(1 @unitT_relT A |- X )0) a2.
  Proof.
    intros. assumption.
  Qed.

  Lemma polyT_relT_unitT_simpl : forall (A : obT), forall X : obT, forall a1 a2, a1 ~~T a2 -> ( @idT (T(0 A |- X )0)  ) a1 ~~T ( T(1I (@IdenT A) |- X )0 ) a2 .
  Proof.
    intros.  intros. assumption.
  Qed.

  (** related to non-variance when unit push the output, commonly  ( (f _i) o> 1 ) ~~ (f _i)  , 
       therefore polyT is injective **)
  Lemma polyT_relT_inputUnitT : forall (V : obT) (B A : obT) (f : T(0 V |- T(0 B |- A )0 )0), forall _v,
                                  f _v ~~T DesIdenObLT( T(1 f |- A )0 <<o  unitT_relT) _v.
  Proof.
    reflexivity.
  Qed.
  
  Lemma polyT_relT_inputUnitT_simpl : forall (B : obT), forall (A : obT),
                                      forall (b : T(0 B |- A )0),
                                        b  ~~T ( (T(1I b |- A )0)  (@IdenT A) ) .
  Proof.
    reflexivity.
  Qed.
End METALOGIC.

Import METALOGIC.

Module LOGIC.
  Set Implicit Arguments.
  Unset  Strict Implicit.

  (**  put any `arrows :^) logic'  V   ...  this says that rewrite polyV_relT more generally as if enriched in T  then get old instance... therefore must rewrite polyV_relT_polymorphism more generally then get old instance  **)

  Record data :=
    Data {
        obV : Type;
        polyV_relT00 : obV -> obV -> obT;
        convV : forall V1 V2, polyV_relT00 V1 V2 -> polyV_relT00 V1 V2 -> Prop;
        polyV_relT : forall (T : obT), forall B : obV,  forall (A : obV),
                       T(0 T |- (polyV_relT00 B A) )0 ->
                       forall (X : obV), T(0 (polyV_relT00 A X) |-  T(0 T |- (polyV_relT00 B X) )0 )0;
        IdenV : forall {V : obV}, (polyV_relT00 V V);

        consV00 : obV -> obV -> obV;
        consV01 : forall V1 : obV, forall {V2 V2'}, (polyV_relT00 V2 V2') -> (polyV_relT00 (consV00 V1 V2)  (consV00 V1 V2'));
        consV10 : forall {V1' V1}, (polyV_relT00 V1' V1) -> forall V2 : obV, (polyV_relT00 (consV00 V1 V2) (consV00 V1' V2));
        desV00 : forall V2 : obV, forall V1 : obV, obV;
        desV10 : forall V2 : obV, forall {V1 V1'}, (polyV_relT00 V1 V1') -> (polyV_relT00 (desV00 V2 V1) (desV00 V2 V1'));
        Cons : forall {V : obV}, forall {U W : obV}, (polyV_relT00 (desV00 V U) W) -> (polyV_relT00 U (consV00 V W));
        Des : forall {V : obV}, forall {U W : obV}, (polyV_relT00 U (consV00 V W)) -> (polyV_relT00 (desV00 V U) W);

        IdenObV : obV;
        unitV : forall {A : obV}, (polyV_relT00 IdenObV (consV00 A A) );
        Assoc : forall {V W :obV}, forall {U: obV}, (polyV_relT00 (desV00 (desV00 W V) U )  ((desV00 W (desV00  V U ))  ) );
        DesIdenObR : forall {U W : obV}, (polyV_relT00 U (consV00 IdenObV W) ) -> (polyV_relT00 U W);
        DesIdenObL : forall {V : obV}, forall {W : obV}, (polyV_relT00 IdenObV (consV00 V W)) -> (polyV_relT00 V W);
      }.

  Arguments Des {_} {_ _ _} _ .
  Arguments Cons {_} {_ _ _} _ .
  Arguments Assoc {_} {_ _ _}.
  Arguments DesIdenObR {_} {_ _} _ .
  Arguments DesIdenObL {_} {_ _} _ .

  Definition polyV_relV00 := (@consV00) .
  
  Module Ex_Notations.
    Notation "dat .-V(0 B |- A )0" := (@polyV_relT00 dat B A) (at level 35, format "dat .-V(0  B  |-  A  )0").
  End Ex_Notations.
  Import Ex_Notations.
  Notation "V(0 B |- A )0" := (_ .-V(0 B |- A )0) (at level 35).

  (** remember these polyV_relT_constant and polyV_relT_identitary forms are non-general and are particular for _relT, because no unit-picking mentionned **)
  Definition polyV_relT_constant {log: data} : forall (B : obV log), forall (A : obV log),
                                                 V(0 B |- A )0 -> forall X : obV log, T(0 V(0 A |- X )0  |- V(0 B |- X )0 )0
    := (fun (B A : obV log) (f : V(0 B |- A )0) (X : obV log) (g : V(0 A |- X )0) =>
          polyV_relT (cstT f) g tt) .
  (*    Arguments polyV_relT_constant : simpl never.*)

  (** remember these polyV_relT_constant and polyV_relT_identitary forms are non-general and are particular for _relT, because no unit-picking mentionned **)
  Definition polyV_relT_identitary {log : data} : forall (B : obV log), forall (A : obV log),
                                                  forall X : obV log, T(0 V(0 A |- X )0  |- T(0 V(0 B |- A )0 |- V(0 B |- X )0 )0 )0
    :=  fun (B : obV log) => fun (A : obV log) =>
                            fun X : obV log =>  fun (a : V(0 A |- X )0) => fun (b : V(0 B |- A )0) =>
                                                                      @polyV_relT log (V(0 B |- A )0) B A (idT) X a b .
  (*    Arguments polyV_relT_identitary : simpl never.*)


  Definition unitV_relT {log : data} : forall {A : obV log}, T(0 IT |- V(0 A |- A )0 )0.
    intros. intro. eapply IdenV.
  Defined.
  
  Module Ex_Notations2.
    Export Ex_Notations.
    Notation "dat .-V(1 b |- X )0" := (@polyV_relT dat _ _ _ b X) (at level 35, format "dat .-V(1  b  |-  X  )0").
    (**  more precisely ( ( b 0 ) o> _ )   **)
    Notation "dat .-V(1I b |- X )0" := (@polyV_relT_constant dat _ _ b X) (at level 35, format "dat .-V(1I  b  |-  X  )0").
    (**  more precisely ( ( b 0 ) o> a )  **)
    (*TODO: write this as coming from application ( b o>dat> ) a *)
    Notation "b o> dat > a" := (@polyV_relT_constant dat _ _ b _ a) (at level 33, right associativity, dat at next level, format "b  o> dat >  a").
    Notation "dat .-V(0 X |- - )1" := (@polyV_relT_identitary dat _ _ X) (at level 35, format "dat .-V(0  X  |-  -  )1").
    (**  more precisely ( ( id _ ) o> a )  **)
    Notation "dat .-V(0 X |- a )1" := (@polyV_relT_identitary dat _ _ X a) (at level 35, format "dat .-V(0  X  |-  a  )1").
    (**  more precisely ( ( id b ) o> a )  **)
    (*TODO: write this as coming from application ( a <<o ) a *)
    Notation "a < dat <o b" := (@polyV_relT_identitary dat _ _ _ a b) (at level 33, right associativity, dat at next level, format "a  < dat <o  b").

    Notation "v2 ~~ dat ` v1" := (@convV dat _ _ v2 v1)  (at level 70, dat at next level, format "v2  ~~ dat `  v1").
    Notation "dat .-1" := (@IdenV dat _) (at level 0, format "dat .-1").
    Notation "dat .-[0 V1 ~> V2 ]0" := (@consV00 dat V1 V2) (at level 30, format "dat .-[0  V1  ~>  V2  ]0").
    Notation "dat .-[0 V1 ~> v ]1" := (@consV01 dat V1 _ _ v) (at level 30, format "dat .-[0  V1  ~>  v  ]1").
    Notation "dat .-[1 v ~> V2 ]0" := (@consV10 dat _ _ v V2) (at level 30, format "dat .-[1  v  ~>  V2  ]0").
    Notation  "dat .-(0 V1 & V2 )0" := (@desV00 dat V2 V1) (at level 30, format "dat .-(0  V1  &  V2  )0").
    Notation  "dat .-(1 v & V2 )0" := (@desV10 dat V2 _ _ v) (at level 30, format "dat .-(1  v  &  V2  )0").
    Notation "dat .-V[0 V1 ~> V2 ]0" := (@polyV_relV00 dat V1 V2) (at level 25, only parsing).
    Notation  "dat .-I" := (@IdenObV dat ) (at level 0, format "dat .-I").
    Notation "dat .-uV" := (@unitV dat _) (at level 0, format "dat .-uV").
  End Ex_Notations2.
  Import Ex_Notations2.
  Notation "V(1 b |- X )0" := (_ .-V(1 b |- X )0) (at level 35, format "V(1  b  |-  X  )0").
  Notation "V(1I b |- X )0" := (_ .-V(1I b |- X )0) (at level 35, format "V(1I  b  |-  X  )0").
  (*TODO: write this as coming from application ( b o> ) a *)
  Notation "b o> a" := (b o> _ > a) (at level 33, right associativity).

  Notation "V(0 X |- - )1" := (_ .-V(0 X |- - )1) (at level 35, format "V(0  X  |-  -  )1").
  Notation "V(0 X |- a )1" := (_ .-V(0 X |- a )1) (at level 35, format "V(0  X  |-  a  )1").
  (*TODO: write this as coming from application ( a <o ) b *)
  Notation "a <o b" := (a < _ <o b) (at level 33, right associativity).

  Notation "v2 ~~ v1" := (@convV _ _ _ v2 v1)  (at level 70).
  Notation "1" := (_ .-1) (at level 0).
  Notation "[0 V1 ~> V2 ]0" := (_ .-[0 V1 ~> V2 ]0) (at level 30, format "[0  V1  ~>  V2  ]0").
  Notation "[0 V1 ~> v ]1" := (_ .-[0 V1 ~> v ]1) (at level 30, format "[0  V1  ~>  v  ]1" ).
  Notation "[1 v ~> V2 ]0" := (_ .-[1 v ~> V2 ]0) (at level 30, format "[1  v  ~>  V2  ]0").
  Notation  "(0 V1 & V2 )0" := (_ .-(0 V1 & V2 )0) (at level 30, format "(0  V1  &  V2  )0").
  Notation  "(1 v & V2 )0" := (_ .-(1 v & V2 )0) (at level 30, format "(1  v  &  V2  )0").
  Notation "V[0 V1 ~> V2 ]0" := (_ .-V[0 V1 ~> V2 ]0) (at level 25, only parsing).
  Notation  "'I'" := (_ .-I) (at level 0).
  Notation "'uV'" := (_ .-uV) (at level 0).

  (** Class not critical, only for easy proofs without doing (class_of _) **)
  Class class {dat : data} :=
    Class {
        ReflV : forall (A1 A2 : obV dat) (f : V(0 A1 |- A2 )0), f ~~ f;
        TransV : forall (A1 A2 : obV dat) , forall (uTrans f : V(0 A1 |- A2)0), uTrans ~~ f -> forall (f' : V(0 A1 |- A2)0), f' ~~ uTrans -> f' ~~ f;
        SymV : forall (A1 A2 : obV dat),  forall (f' f : V(0 A1 |- A2)0), f ~~ f' -> f' ~~ f;
        Cong_polyV_relT :   forall (V : obT) (B A : obV dat) (f f' : T(0 V |- V(0 B |- A )0 )0),
                              (forall _v : V, f' _v ~~ f _v) -> forall X : obV dat,  forall a1 a2, a1 ~~ a2 -> forall _v, V(1 f' |- X )0 a1 _v ~~ V(1 f |- X )0 a2 _v;
        (** remember that polyV_relT_arrow , relate in particular the polyV_relT_constant to polyV_relT_identitary **)
        polyV_relT_arrow : forall (B A : obV dat) (V V' : obT) (v : T(0 V' |- V )0)
                             (f : T(0 V |- dat.-V(0 B |- A )0 )0) (X : obV dat),
                           forall (a : dat.-V(0 A |- X )0) a0, a ~~ a0 ->  forall (_v': V'),
                                                                      (dat.-V(1 f <<o v |- X )0) a _v' ~~
                                                                                                ([1T v ~> dat.-V(0 B |- X )0 ]0 <<o (dat.-V(1 f |- X )0)) a0 _v';
        (** written here :   (outer modification) ~~ (inner modification) **)
        polyV_relT_morphism : forall (V : obT) (B A : obV dat) (W : obT) (A' : obV dat)
                                (g : T(0 W |- dat.-V(0 A |- A' )0 )0)
                                (f : T(0 V |- dat.-V(0 B |- idT A )0 )0) (X : obV dat), forall (a' : V(0 idT A' |- X )0) (_w_v : (0T W & V )0),
                                dat.-V(1 DesT ([1T f ~> dat.-V(0 B |- idT A' )0 ]0 <<o (dat.-V(1 '1T |- A' )0) <<o g) |- X )0 a' _w_v
                                   ~~ DesInT ([0T W ~> dat.-V(1 f |- X )0 ]1 <<o (dat.-V(1 g |- X )0)) a' _w_v;
        (** related to non-variance when unit pull the input, commonly  ( 1 o> h ) ~~ h  **)
        polyV_relT_unitV : forall A X : obV dat, forall a1 a2, a1 ~~ a2 ->
                                                     @IdenT _ a1 ~~ DesIdenObRT (dat.-V(1 @unitV_relT _ A |- X )0) a2;
        (** related to non-variance when unit push the output, commonly  ( (f _i) o> 1 ) ~~ (f _i)  , 
       therefore polyV is injective **)
        polyV_relT_inputUnitV : forall (V : obT) (B A : obV dat) (f : T(0 V |- V(0 B |- A )0 )0), forall _v,
                                  f _v ~~ DesIdenObLT( V(1 f |- A )0 <<o  unitV_relT) _v;
        CongDes : forall V : obV dat, forall (U W : obV dat), forall (f f' : V(0 U |- [0 V ~> W ]0 )0),
                    f' ~~ f -> Des f' ~~ Des f ;
        Des_Cons : forall V : obV dat, forall (U W : obV dat), forall (f : V(0 (0 U & V )0 |-  W )0),
                     Des (Cons f) ~~ f ;
        Des_Output : forall V : obV dat, forall (U W : obV dat), forall (v : V(0 U |- [0 V ~> W ]0 )0), forall W' (w : V(0 W |- W' )0),
                       Des( [0 V ~> w ]1 <o v ) ~~ w <o Des( v ) ;
        CongCons : forall V : obV dat, forall (U W : obV dat), forall (v v' : V(0 (0 U & V )0 |- W )0 ),
                     v' ~~ v -> Cons v' ~~ Cons v ;
        Cons_Des : forall V : obV dat, forall (U W : obV dat), forall (f : V(0 U |-  [0 V ~> W ]0 )0),
                     Cons (Des f) ~~ f ;
        Cons_Input : forall V : obV dat, forall (U U' : obV dat) (w : V(0 U' |- U )0), forall (W : obV dat) (v : V(0 (0 U & V )0 |- W )0),
                       Cons(v <o (1 w & V )0 )  ~~ Cons( v ) <o w ;
        Assoc_Rev : forall{V W U : obV dat},
                      V(0 (0(0U & V )0 & W )0 |- (0U & (0V & W )0 )0 )0;
        Assoc_Assoc_Rev : forall(V W U : obV dat),
                            1 ~~ (Assoc_Rev <o (@Assoc dat V W U));
        Assoc_Rev_Assoc : forall(V W U : obV dat),
                            1 ~~ ((@Assoc dat V W U) <o Assoc_Rev);
      }.

  Arguments ReflV {_ _} _ _ _ .
  Arguments TransV {_ _} _ _ _ _ _ _ _ .
  Arguments SymV {_ _} _ _ _ _ _ .
  Arguments Cong_polyV_relT {_ _} [_ _ _ _ _ _ _ _]  _ _ _ .
  Arguments polyV_relT_arrow {_ _} {_ _ _ _} _ _ {_ _ _} _ _ .
  Arguments polyV_relT_morphism {_ _} {_ _ _ _ _} _ _ {_} _ _ .
  Arguments polyV_relT_unitV {_ _} [_ _ _ _] _ .
  Arguments polyV_relT_inputUnitV {_ _} {_ _ _} _ _ .
  Arguments CongDes {_ _} [_ _ _ _ _] _ .
  Arguments Des_Cons {_ _} [_ _ _] _ .
  Arguments Des_Output {_ _} [_ _ _ _ _] _ .
  Arguments CongCons {_ _} [_ _ _] _ _ _.
  Arguments Cons_Des {_ _} [_ _ _ _] .
  Arguments Cons_Input {_ _} [_ _ _ _ _] _ .
  Arguments Assoc_Rev {_ _} {_ _ _} .

  Structure logic :=
    Logic {
        data_of :> data;
        class_of :> @class data_of
      }.

  (** not critical, only for easy proofs without doing (class_of _) **)
  Existing Instance class_of.
  
  Section Context.
    Context {log : logic}.

    Lemma polyV_relT_arrow_simpl : forall (B : obV log) (A : obV log) (V V' : obT) (v : V' -> V),
                                   forall (f : V -> V(0 B |- A )0 ) (X : obV log),
                                   forall (a : V(0 A |- X )0) a0, a ~~ a0 -> forall (_v' : V'),
                                                                        V(1 f <<o v |- X )0 a _v'
                                                                         ~~   V(1 f |- X )0 a0 (v _v').
    Proof.
      intros. eapply polyV_relT_arrow. assumption.
    Qed.

    Lemma polyV_relT_unitV_simpl : forall (A X : obV log), forall a1 a2, a1 ~~ a2 -> ( @idT (V(0 A |- X )0)  ) a1 ~~ ( V(1I (@IdenV _ A) |- X )0 ) a2.
    Proof.
      intros. eapply polyV_relT_unitV. assumption.
    Qed.

    Lemma polyV_relT_inputUnitV_simpl : forall (B : obV log), forall (A : obV log),
                                        forall (b : V(0 B |- A )0),  b  ~~ ( (V(1I b |- A )0)  (@IdenV _ A) ).
    Proof.
      intros. eapply polyV_relT_inputUnitV with (f:=(fun _ : unit => b)).
    Qed.

    Definition ConsIn : forall V : obV log, forall (U0 U1 W : obV log), V(0 U0 |- [0 (0 U1 & V )0 ~> W ]0 )0 -> V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0 .
      intros. apply Cons. apply Cons. Check @Assoc. eapply polyV_relT_identitary. eapply Des.  2:  eapply Assoc_Rev. exact H.
    Defined.

    Definition polyV_relV :  forall (U : obV log), forall (W : obV log), forall (V : obV log),
                               V(0 U |- [0 W ~> V ]0 )0 ->
                               forall X : obV log, V(0 [0 V ~> X ]0  |- [0 U ~> [0 W ~> X ]0 ]0 )0 .
      intros ? ? ? v ?.  exact  (ConsIn( [1 Des v ~> X]0)).
    Defined.

    Lemma CongConsIn : forall V : obV log, forall (U0 U1 W : obV log), forall (v v' : V(0 U0 |- [0 (0 U1 & V )0 ~> W ]0 )0),
                         v' ~~ v -> ConsIn v' ~~ ConsIn v .
    Admitted.

    Definition DesIn : forall {V : obV log}, forall {U0 U1 W : obV log}, V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0 -> V(0 U0 |- [0 (0 U1 & V )0 ~> W ]0 )0.
      intros. apply Cons. eapply polyV_relT_identitary. Check @Assoc. 2: eapply Assoc. eapply Des.
      eapply Des. exact H.
    Defined.
    
    (* polyV_relT_constant_rel_identitary  :  b o> a ~~ a <o b *)
    Lemma polyV_relT_constant_rel_identitary :  forall (B : obV log) , forall (A : obV log) ,
                                                forall X : obV log , forall (a : V(0 A |- X )0),  forall (b : V(0 B |- A )0),
                                                  @polyV_relT_constant log B A b X a  ~~  a <o b .
    Proof.
      unfold polyV_relT_identitary. unfold polyV_relT_constant.
      intros.  eapply (@polyV_relT_arrow _ log) with (f := fun b0 => b0) (v := fun _ : unit => b). eapply ReflV.
    Qed.

    Lemma Cong_polyV_relT_constant : forall (B : obV log), forall (A : obV log),
                                     forall (f f' : V(0 B |- A )0), f' ~~ f -> forall X : obV log,
                                                                        forall a1 a2, a1 ~~ a2 -> @polyV_relT_constant log B A f' X a1 ~~  @polyV_relT_constant _ B A f X a2.
    Proof.
      intros. eapply  (@Cong_polyV_relT _ log)  with (f:=fun _ : unit => f)  (f':=fun _ : unit => f'); intros; assumption.
    Qed.
    Arguments Cong_polyV_relT_constant [_ _ _ _ _ _ _] _ _ .

    Lemma CongCom_identitary : forall (A2 A3 : obV log), forall (f2 f2' : V(0 A2 |- A3 )0), f2 ~~ f2' -> forall A1, forall (f1 f1' : V(0 A1 |- A2 )0), f1 ~~ f1' -> f2 <o f1 ~~ f2' <o f1'.
    Proof.
      intros. eapply TransV; [ eapply polyV_relT_constant_rel_identitary |].
      eapply TransV; [| eapply SymV, polyV_relT_constant_rel_identitary].
      eapply Cong_polyV_relT_constant;  assumption.
    Qed.
    
    Lemma CongCom_constant : forall (A2 A3 : obV log), forall (f2 f2' : V(0 A2 |- A3 )0), f2 ~~ f2' -> forall A1, forall (f1 f1' : V(0 A1 |- A2 )0), f1 ~~ f1' -> f1 o> f2 ~~ f1' o> f2'.
    Proof.
      intros. eapply Cong_polyV_relT_constant;  assumption.
    Qed.

    Lemma polyV_relT_morphism_simpl : forall (B : obV log), 
                                      forall (A : obV log) (A' : obV log) (g : V(0 A |- A')0),
                                      forall (X : obV log), forall (pull : V(0 B |- A)0), forall (push : V(0 A'  |- X )0 ),
                                        V(1I V(0 A' |- g )1 pull |- X )0 push
                                         ~~ V(0 X |- V(1I g |- X )0 push )1 pull.
    Proof.
      intros. generalize (@polyV_relT_morphism log log). intros H_polyV_relT_morphism.
      specialize H_polyV_relT_morphism with (V:=unit)(B:=B)(A:=A)(W:=unit)(g:=(fun _ : unit => g))(f:=(fun _ : unit => pull))(X:=X)(a':=push)(_w_v:=(tt,tt)).
      unfold polyV_relT_constant. unfold polyV_relT_identitary.
      unfold DesInT, DesT, ConsT, AssocT, polyT_relT_identitary, polyT_relT, consT10, consT01, idT, cstT in H_polyV_relT_morphism.
      eapply TransV in H_polyV_relT_morphism; [|eapply polyV_relT_arrow with (f := idT); eapply ReflV].
      unfold DesInT, DesT, ConsT, AssocT, polyT_relT_identitary, polyT_relT, consT10, consT01, idT, cstT in H_polyV_relT_morphism.
      (* remember that polyV_relT_arrow , relate in particular the polyV_relT_constant to polyV_relT_identitary *)
      eapply SymV, TransV, SymV in H_polyV_relT_morphism; [|eapply polyV_relT_arrow with (f:=idT); eapply ReflV].
      eapply TransV; [| eapply polyV_relT_arrow with (v:=fun _ : unit => (V(1 idT |- _ )0) g pull) (f:=idT); eapply ReflV].
      unfold DesInT, DesT, ConsT, AssocT, polyT_relT_identitary, polyT_relT, consT10, consT01, idT, cstT in H_polyV_relT_morphism |- *.
      eapply H_polyV_relT_morphism.
    Qed.

    Lemma CongDesIn : forall V : obV log, forall (U0 U1 W : obV log), forall (v v' : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0),
                        v' ~~ v -> DesIn v' ~~ DesIn v.
    Admitted.

    Lemma ConsIn_DesIn : forall V : obV log, forall (U0 U1 W : obV log), forall (f : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0),
                           ConsIn (DesIn f) ~~ f .
    Admitted.
    
    Lemma DesIn_Input : forall V : obV log, forall (U0 U1 W : obV log), forall (v : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0), forall (U0' : obV log) (i : V(0 U0' |- U0 )0),
                          (DesIn v) <o i ~~ DesIn( v <o i ) .
    Admitted.
    Lemma Des_Input : forall (U U' : obV log) (w : V(0 U' |- U )0), forall (V W : obV log) (v : V(0 U |- [0 V ~> W ]0 )0), 
                        Des( v <o w ) ~~ Des( v ) <o desV10 V w .
    Admitted.
    Lemma ConsIn_Output : forall V : obV log, forall (U0 : obV log), forall (U1 U1' : obV log) (u1 : V(0 U1' |- U1 )0), forall (W : obV log), forall (v : V(0 U0 |- [0 (0 U1 & V )0 ~> W ]0 )0),
                            ConsIn( [1 (1 u1 & V )0 ~> W ]0 <o v ) ~~ [1 u1 ~> [0 V ~> W ]0 ]0 <o ConsIn( v ) .
    Admitted.
    Lemma CongConsV01 : forall V1 : obV log, forall (V2 V2' : obV log) (v v' : V(0 V2 |- V2' )0),
                          v' ~~ v -> [0 V1 ~> v' ]1 ~~ [0 V1 ~> v ]1 .
    Admitted.
    Lemma ConsIn_Input : forall V : obV log, forall (U0 U1 W : obV log), forall (v : V(0 U0 |- [0 (0 U1 & V )0 ~> W ]0 )0), forall (U0' : obV log) (i : V(0 U0' |- U0 )0),
                           ConsIn( v <o i ) ~~ (ConsIn v) <o i .
    Admitted.
    Lemma consV01_functorial : forall V1 : obV log, forall V2 V2' (v : V(0 V2 |- V2' )0), forall V2'' (v' : V(0 V2' |- V2'' )0),
                                 [0 V1 ~> v' <o v ]1 ~~  [0 V1 ~> v' ]1 <o  [0 V1  ~> v ]1 .
    Admitted.
    Lemma DesIn_ConsIn : forall V : obV log, forall (U0 U1 W : obV log), forall (f : V(0 U0 |- [0 (0 U1 & V )0 ~> W ]0 )0),
                           DesIn (ConsIn f) ~~ f.
    Admitted.
    Lemma Assoc_Iso : forall (V W : obV log), forall (U: obV log),
                      forall (Y X : obV log) (f g : V(0 Y |-  [0 (0 ((0 U & V )0) & W )0 ~> X ]0 )0 ), 
                        [1 Assoc ~> X ]0 <o f ~~ [1 Assoc  ~> X ]0 <o g -> f ~~ g .
    Admitted.
    Lemma Assoc_nat0 : forall (V W : obV log), forall (U U' : obV log) (f : V(0 U |- U' )0 ),
                         Assoc <o (1 f & (0 V & W )0 )0 ~~ (1 ((1 f & V )0) & W )0 <o Assoc .
    Admitted.
    Lemma Des_consV10_functorial : forall V B PA (f : V(0 V |- [0 B ~> PA ]0 )0) PA' QA (g : V(0 [0 B ~> PA ]0 |- [0 B ~> QA ]0 )0) ,
                                     (Des ([1 Des (g <o f) ~> PA' ]0 ))
                                       ~~ ( ( Des (Des ([1 f ~> [0 B ~> PA' ]0 ]0 <o ConsIn ([1 Des (g) ~> PA' ]0))) ) <o Assoc
                                            : V(0 (0 ([0 QA ~> PA' ]0) & (0V & B )0 )0 |- PA' )0 ).
    Admitted.
    (** Lemma Assoc_Des_Des_old : forall V B PA PA' (f : V(0 V |- [0 B ~> PA ]0 )0),
                                     ( (Des ([1 Des f ~> PA' ]0 )) : V(0 (0 ([0 PA ~> PA' ]0) & (0V & B )0 )0 |- PA' )0 )
                                       ~~ ( ( Des (Des ([1 f ~> [0 B ~> PA' ]0 ]0 <o ConsIn ([1 Des (@IdenV ([0 B ~> PA ]0)) ~> PA' ]0))) ) <o Assoc ). **)
    Lemma Assoc_DesIn_DesIn :  forall W PX, forall  V B PA (f : V(0 V |- [0 B ~> PA ]0 )0),
                                 DesIn ([0 W ~>  ([1 Des f ~> PX ]0) ]1)
                                       ~~ [1 Assoc ~> PX ]0 <o DesIn( DesIn ([0 W ~>  ConsIn([1 Des f ~> PX ]0) ]1) ) .
    Admitted.

    Lemma Cons_Output : forall V : obV log, forall (U W : obV log), forall (v :  V(0 (0 U & V )0 |-  W )0), forall W' (w : V(0 W |- W' )0),
                          [0 V ~> w ]1 <o Cons( v ) ~~ Cons( w <o v ) .
    Admitted.
    Lemma ConsIn_Output2 : forall V : obV log, forall (U0 : obV log), forall (U1 : obV log) , forall (W W' : obV log) (w : V(0 W |- W' )0), forall (v : V(0 U0 |- [0 (0 U1 & V )0 ~> W ]0 )0),
                             ConsIn( [0 (0 U1 & V )0 ~> w ]1 <o v ) ~~ [0 U1 ~> [0 V ~> w ]1 ]1 <o ConsIn( v ) .
    Admitted.
    Lemma ConsIn_consV10_functorial : forall V B PA (f : V(0 V |- [0 B ~> PA ]0 )0) PA' QA (g : V(0 [0 B ~> PA ]0 |- [0 B ~> QA ]0 )0),
                                        ( ConsIn (([1 Des (g <o f) ~> PA' ]0)) )
                                          ~~ ( ([1 f ~> [0 B ~> PA' ]0 ]0 <o ConsIn ([1 Des (g) ~> PA' ]0))
                                               : V(0 [0 QA ~> PA' ]0 |- [0 V ~> [0 B ~> PA' ]0 ]0 )0 ) .
    Admitted.

    Lemma Des_I_Iso : forall (A : obV log),
                      forall (Y X : obV log) (f g : V(0 Y |-  [0  A ~> X ]0 )0 ), 
                        [1 Des (@IdenV _ ([0 I ~> A ]0)) ~> X ]0 <o f ~~ [1  Des (@IdenV _ ([0 I ~> A ]0))  ~> X ]0 <o g -> f ~~ g .
    Admitted.
  End Context.

  Module Ex_Notations3.
    Export Ex_Notations2.
    Notation "dat .-V[1 v ~> X ]0" := (@polyV_relV dat _ _ _ v X) (at level 25).
    Notation "dat .-V[0 X ~> w ]1" := ((@polyV_relV dat _ _ _ 1 X) <dat<o w) (at level 25).
    Notation "dat .-V[0 W ~> - ]1" := (fun V X => @polyV_relV dat _ _ _ (@IdenV dat (dat.-V[0 W ~> V ]0)) X) (at level 25).
  End Ex_Notations3.
  Import Ex_Notations3.
  Notation "V[1 v ~> X ]0" := (_ .-V[1 v ~> X ]0) (at level 25).
  Notation "V[0 X ~> w ]1" := (_ .-V[0 X ~> w ]1) (at level 25).
  Notation "V[0 W ~> - ]1" := (_ .-V[0 W ~> - ]1) (at level 25).

  Section Context2.
    Context {log : logic}.

    Lemma polyV_relV_polyV_relT : forall (W : obV log), forall (U : obV log) (V : obV log),
                                  forall (v : V(0 U |- [0 W ~> V ]0 )0), forall X : obV log,
                                    [1 Des v ~> X]0
                                                  ~~ DesIn( V[1 v ~> X ]0 ) .
    Admitted.

    (** TODO: PUT IN DATA OR CLASS **)
    Axiom CongDesIdenObR : forall (U W : obV log), forall (v v' : V(0 U |- [0 I ~> W ]0 )0),
                             v' ~~ v -> DesIdenObR v' ~~ DesIdenObR v .
    Axiom DesIdenObR_output : forall (U : obV log) (W W' : obV log) (w : V(0 W |- W' )0), forall v : V(0 U |- [0 I ~> W ]0 )0, 
                                DesIdenObR( [0 I ~> w ]1 <o v ) ~~ w <o DesIdenObR( v ) .
    Axiom DesIdenObR_Input : forall (U W : obV log) (U' : obV log) (w : V(0 U' |- U )0), forall v : V(0 U |- [0 I ~> W ]0 )0, 
                               DesIdenObR( v <o w ) ~~ DesIdenObR( v ) <o w .
    Axiom DesIdenObRInCons : forall (U W : obV log),
                               [1 DesIdenObR (Cons (@IdenV _ ((0 U & I )0))) ~> W ]0 ~~
                                                                                   ([0 U ~> DesIdenObR (@IdenV _ ([0 I ~> W ]0)) ]1 <o
                                                                                                                                       ConsIn (@IdenV _ ([0 (0 U & I )0 ~> W ]0)) 
                                                                                    : V(0 [0 (0 U & I )0 ~> W ]0 |- [0 U ~> W ]0 )0 ) .

    Axiom CongDesIdenObL : forall (V W : obV log), forall (v v' : V(0 I |- [0 V ~> W ]0 )0),
                             v' ~~ v -> DesIdenObL v' ~~ DesIdenObL v .
    Parameter ConsIdenObL : forall V : obV log, forall (W : obV log), V(0 V |- W )0 -> V(0 I |- [0 V ~> W ]0 )0 .
    Axiom ConsIdenObL_DesIdenObL : forall V : obV log, forall (W : obV log), forall v : V(0 I |- [0 V ~> W ]0 )0,
                                     v ~~ ConsIdenObL( DesIdenObL v) .
    Axiom DesIdenObR_ConsIdenObL : forall V : obV log, forall v : V(0 I |- V )0,
                                     v ~~ DesIdenObR( ConsIdenObL v) .
    Axiom Des_ConsIn :  forall V : obV log, forall (U1 W : obV log), forall (v : V(0 I |- [0 (0 U1 & V )0 ~> W ]0 )0),
                          DesIdenObL (v) ~~ Des (DesIdenObL (ConsIn (v))).
    Axiom DesIdenObRConsIdenObL : forall (V W : obV log),
                                    (@IdenV log ([0 V ~> W ]0)) ~~ DesIdenObR (ConsIn ([1 Des (ConsIdenObL 1) ~>  W ]0)).
    Axiom CongConsIdenObL : forall V : obV log, forall (W : obV log), forall (v v' : V(0 V |- W )0),
                              v' ~~ v -> ConsIdenObL v' ~~ ConsIdenObL v .
    Axiom consV10_functorial : forall (V1' V1 : obV log) (v :  V(0 V1' |- V1 )0), forall V1'' (v' : V(0 V1'' |- V1' )0), forall V2 : obV log,
                                 [1 v <o v' ~> V2 ]0 ~~  [1 v' ~> V2 ]0 <o  [1 v ~> V2 ]0 .
    Axiom consV11_bifunctorial : forall (V1' V1 : obV log) (v : V(0 V1' |- V1 )0), forall W1 W1' (w : V(0 W1 |- W1' )0),
                                   [0 V1' ~> w ]1 <o  [1 v ~> W1 ]0 ~~ [1 v ~> W1' ]0 <o [0 V1 ~> w ]1 .
    Axiom CongConsV10 : forall (V1' V1 : obV log) (v v' : V(0 V1' |- V1)0), forall V2 : obV log,
                          v' ~~ v -> [1 v' ~> V2 ]0 ~~ [1 v ~> V2 ]0 .

    
    Axiom consV10_DesIdenObL : forall U : obV log, forall V : obV log, forall (W : obV log), forall (v : V(0 I |- [0 V ~> W ]0 )0), 
                                 [1 DesIdenObL  v ~> U ]0  ~~ DesIdenObR( ConsIn( [1 Des v ~> U ]0 ) ) .  (*/!\SAME/!\*)Axiom DesIdenObR_DesIdenObL : forall ( V W X : obV log) (v : V(0 I |- [0 V ~> W ]0 )0),
                                                                                                                                                        [1 DesIdenObL v ~> X ]0 ~~ DesIdenObR (ConsIn ([1 Des v ~> X ]0)) .

    Axiom consV10_functorial_fun1 : forall V1, forall V2 : obV log,
                                      (@IdenV _ _) ~~    [1 (@IdenV _ V1) ~> V2 ]0 .

    
    (** remember that  unitV is not really primitive **)
    Axiom unitV_IdenV : forall A : obV log,  (@IdenV log A) ~~ DesIdenObL (@unitV log A).

    (** even/same for these that the decision are recursively-decidable because still purely logical after unfolding polyV_relV **) 
    Lemma CongPolyV : forall (V B A : obV log) (f f' : V(0 V |- V[0 B ~> A ]0 )0),
                        f' ~~ f -> forall X : obV log, V[1 f' ~> X ]0 ~~ V[1 f ~> X ]0 .
    Admitted.

    Lemma polyV_relV_arrow :  forall (B : obV log) (A : obV log) (V : obV log),
                              forall (V' : obV log) (v : V(0 V' |- V )0),
                              forall (f : V(0 V |- [0 B ~> A ]0 )0) (X : obV log),
                                V[1 (f <o v) ~> X ]0
                                 ~~ [1 v ~> [0 B ~> X ]0 ]0 <o (V[1 f ~>  X ]0) .
    Admitted.

    Lemma polyV_relV_morphism :  forall (V B A W A' : obV log) (g : V(0 W |-V[0 A ~> A' ]0 )0)
                                   (f : V(0 V |- V[0 B ~> idT A ]0 )0) (X : obV log),
                                   V[1 Des ([1 f ~> [0 B ~> idT A' ]0 ]0 <o V[0 A' ~> g ]1) ~> X ]0 ~~
                                    DesIn ([0 W ~> V[1 f ~> X ]0 ]1 <o V[1 g ~> X ]0) .
    Admitted.

    Lemma polyV_relV_unitV : forall (A : obV log), forall X : obV log, (@IdenV log (V[0 A ~> X ]0)) ~~ DesIdenObR( V[1 (@unitV log A) ~> X ]0 ) .
    Admitted.
    Lemma polyV_relV_inputUnitV :forall (V : obV log),  forall (B : obV log),  forall (A : obV log),
                                 forall (f : V(0 V |- V[0 B ~> A ]0 )0),
                                   f  ~~ DesIdenObL( (V[1 f ~> A ]0) <o (@unitV log A) ).
    Admitted.


    (**  Section: common categories *)

    Definition ComV : forall (V1 : obV log), forall UCom, V(0 V1 |-  UCom )0 -> forall V3, V(0 UCom |- V3 )0 -> V(0 V1 |- V3 )0 := polyV_relT_constant .

    Definition CongCom := (@CongCom_identitary).

    Lemma Cat2V : forall (A3 A4 : obV log) (f3 : V(0 A3 |- A4)0), forall A2 (f2 : V(0 A2 |- A3)0), forall A1 (f1 : V(0 A1 |- A2)0),
                    (f3 <o f2) <o f1 ~~ f3 <o (f2 <o f1).
    Proof.
      intros. eapply TransV; [ eapply polyV_relT_constant_rel_identitary  |].
      eapply TransV; [| eapply CongCom; [|eapply ReflV]; eapply SymV, polyV_relT_constant_rel_identitary  ].
      apply SymV, polyV_relT_morphism_simpl.
      (* OLD DEFINITIONALLY intros. apply SymV, polyV_relT_morphism. *) 
    Qed.

    Lemma Cat1RightV : forall (A1 A2 : obV log), forall f : V(0 A1 |- A2)0,  f ~~ f <o 1.
    Proof.
      intros. eapply TransV; [ eapply polyV_relT_constant_rel_identitary |].
      apply polyV_relT_unitV.
      apply ReflV.
    Qed.
    
    Lemma Cat1LeftV : forall (A1 A2 : obV log), forall f : V(0 A1 |- A2)0,  f ~~ 1 <o f.
    Proof.
      intros. eapply TransV; [ eapply polyV_relT_constant_rel_identitary |].
      apply polyV_relT_inputUnitV_simpl. 
    Qed.      
  End Context2.

  Canonical Structure logT : logic :=
    @Logic _ (@Class
                (@Data obT polyT_relT00 convT polyT_relT 
                       (@IdenT) consT00 (@consT01) consT10 desT00 desT10 ConsT DesT
                       IdenObT (@unitT) (@AssocT) (@DesIdenObRT) (@DesIdenObLT))
                ReflT TransT SymT Cong_polyT_relT polyT_relT_arrow
                polyT_relT_morphism polyT_relT_unitT polyT_relT_inputUnitT CongDesT
                Des_ConsT Des_OutputT CongConsT Cons_DesT Cons_InputT (@Assoc_RevT) Assoc_Assoc_RevT Assoc_Rev_AssocT).
End LOGIC.

Module FUNCTOR.
  Export LOGIC.
  Set Implicit Arguments.
  Unset Strict Implicit.

  Section Context.
    Context {log : logic}.

    Record data :=
      Data {
          obA : Type;
          polyA00 : obA -> obA -> obV log;
          polyA : forall (V : obV log), forall (A2 : obA), forall (A1 : obA),
                    V(0 V |- (polyA00 A2 A1) )0 ->
                    forall X : obA, V(0 (polyA00 A1 X)  |- [0 V ~> (polyA00 A2 X) ]0 )0;
          obB : Type;
          polyB00 : obB -> obB -> obV log;
          polyB : forall (V : obV log), forall (B2 : obB),  forall(B1 : obB),
                    V(0 V |- (polyB00 B2 B1) )0 ->
                    forall Y : obB, V(0 (polyB00 B1 Y)  |- [0 V ~> (polyB00 B2 Y) ]0 )0;
          polyF0 : obA -> obB;
          polyF : forall (V : obV log) (B : obB) (A : obA),
                    V(0 V |- (polyB00 B (polyF0 A)) )0 ->
                    forall X : obA, V(0 (polyA00 A X)  |- [0 V ~> (polyB00 B (polyF0 X)) ]0 )0;
          unitA : forall {A : obA}, V(0 I |- (polyA00 A A) )0;
        }.
    
  End Context.

  Module Ex_Notations3.
    Notation "dat .-A[0 A1 ~> A2 ]0" := (@polyA00 _ dat A1 A2) (at level 25, format "dat .-A[0  A1  ~>  A2  ]0").
    (** therefore "A[1 f ~> X ]0" is similar to ( f _3 o> _2 ) **)
    Notation "dat .-A[1 f ~> X ]0" := (@polyA _ dat _ _ _ f X) (at level 25, format "dat .-A[1  f  ~>  X  ]0").
    Notation "dat .-uA" := (@unitA _ dat _) (at level 0, format "dat .-uA").
    
    Notation "dat .-B[0 B1 ~> B2 ]0" := (@polyB00 _ dat B1 B2) (at level 25, format "dat .-B[0  B1  ~>  B2  ]0").
    Notation "dat .-B[1 m ~> Y ]0" := (@polyB _ dat _ _ _ m Y) (at level 25, format "dat .-B[1  m  ~>  Y  ]0").
  End Ex_Notations3.
  Import Ex_Notations3.
  Notation "A[0 A1 ~> A2 ]0" := (_  .-A[0 A1 ~> A2 ]0) (at level 25).
  Notation "A[1 f ~> X ]0" := (_.-A[1 f ~> X ]0) (at level 25).
  Notation "'uA'" := (_ .-uA) (at level 0).
  Notation "B[0 B1 ~> B2 ]0" := (_.-B[0 B1 ~> B2 ]0) (at level 25).
  Notation "B[1 m ~> Y ]0" := (_.-B[1 m ~> Y ]0) (at level 25).

  Section Context2.
    Context {log : logic}.
    Context {dat : @data log}.
    
    Definition polyA_IdenV  : forall (B : obA dat), forall (A : obA dat),
                              forall X : obA dat, V(0 A[0 A ~> X ]0  |- [0 A[0 B ~> A ]0 ~> A[0 B ~> X ]0 ]0 )0
      := (fun B A X => @polyA _ _ (A[0 B ~> A ]0) B A (@IdenV _ (A[0 B ~> A ]0)) X).
    
    Definition polyB_IdenV : forall (B : obB dat), forall (A : obB dat),
                             forall X : obB dat, V(0 B[0 A ~> X ]0  |- [0 B[0 B ~> A ]0 ~> B[0 B ~> X ]0 ]0 )0
      := (fun B A X => @polyB _ _ (B[0 B ~> A ]0) B A (@IdenV _ (B[0 B ~> A ]0)) X).
  End Context2.
  
  Module Ex_Notations4'.
    Export Ex_Notations3.
    Notation "dat .-A[0 B ~> - ]1" := (@polyA_IdenV _ dat B) (at level 25, format  "dat .-A[0  B  ~>  -  ]1").
    (** therefore "A[0 X ~> g ]1" is similar to the common ( _ <o g ) **)
    Notation "dat .-A[0 X ~> a ]1" := ( (dat.-A[0 _ ~> - ]1) _ X <o (a : V(0 _ |- dat.-A[0 _ ~> X ]0 )0)) (at level 25, format "dat .-A[0  X  ~>  a  ]1").      

    Notation "dat .-B[0 B ~> - ]1" := (@polyB_IdenV _ dat B) (at level 25, format "dat .-B[0  B  ~>  -  ]1").
    Notation "dat .-B[0 Y ~> n ]1" := ( (dat.-B[0 _ ~> - ]1) _ Y <o (n : V(0 _ |- dat.-B[0 _ ~> Y ]0 )0)) (at level 25, format "dat .-B[0  Y  ~>  n  ]1").
    
    Notation "dat .-F|0 A" := (@polyF0 _ dat A) (at level 4, right associativity, format "dat .-F|0  A").
    (** :^) **)
    Notation "dat .-F[0 B ~> A ]0" := (dat.-B[0 B ~> (dat.-F|0 A) ]0) (at level 25, format "dat .-F[0  B  ~>  A  ]0").
    (** therefore "F[1 b ~> X ]0" is similar to   ( b o> ( F|1 _ ) )   , alternatively   ( b o>F _ )   **)
    Notation "dat .-F[1 b ~> X ]0" := (@polyF _ dat _ _ _ b X) (at level 25, format "dat .-F[1  b  ~>  X  ]0").
  End Ex_Notations4'.
  Import Ex_Notations4'.
  Notation "A[0 B ~> - ]1" := (_ .-A[0 B ~> - ]1) (at level 25).
  Notation "A[0 X ~> g ]1" := (_.-A[0 X ~> g ]1) (at level 25).
  Notation "B[0 B ~> - ]1" := (_ .-B[0 B ~> - ]1) (at level 25).
  Notation "B[0 Y ~> n ]1" := (_.-B[0 Y ~> n ]1) (at level 25).
  Notation "F|0 A" := (_ .-F|0 A) (at level 4, right associativity).
  Notation "F[0 B ~> A ]0" := (_ .-F[0 B ~> A ]0) (at level 25).
  Notation "F[1 b ~> X ]0" := (_ .-F[1 b ~> X ]0) (at level 25).

  Section Context3.
    Context {log : logic}.
    Context {dat : @data log}.

    Definition polyF_IdenV : forall (B : obB dat) (A : obA dat),
                             forall X : obA dat, V(0 A[0 A ~> X ]0  |- [0 F[0 B ~> A ]0 ~> F[0 B ~> X ]0 ]0 )0
      := (fun B A X => @polyF _ dat (F[0 B ~> A ]0) B A (@IdenV _ (F[0 B ~> A ]0)) X).

  End Context3.

  Module Ex_Notations4.
    Export Ex_Notations4'.
    Notation "dat .-F[0 B ~> - ]1" := (@polyF_IdenV _ dat B) (at level 25, format "dat .-F[0  B  ~>  -  ]1").
    Notation "dat .-F[0 X ~> a ]1" := ( (dat.-F[0 _ ~> - ]1) _ X <o (a : V(0 _ |- dat.-A[0 _ ~> X ]0 )0)) (at level 25, format "dat .-F[0  X  ~>  a  ]1").      

    (** therefore "F[0 X ~> a ]1" is similar to   ( B[0 B ~> ( F|1 a ) ]1 ) which is ( _ o> ( F|1 a ) )  , alternatively  ( _ o>F a )   **)
    Check fun (log : logic) (dat : data) (B : obB dat) =>
            ( dat.-F[0 B ~> - ]1 : forall (A X : obA dat), V(0 dat.-A[0 A ~> X ]0 |- [0 dat.-F[0 B ~> A ]0 ~> dat.-F[0 B ~> X ]0 ]0 )0 ).
    Check fun (log : logic) (dat : data) (_B : obB dat) (_A : obA dat) (X : obA dat) (_W : obV log) (a : V(0 _W |- A[0 _A ~> X ]0 )0) =>
            ( dat.-F[0 X ~> a ]1 : V(0 _W |- [0 dat.-F[0 _B ~> _A ]0 ~> dat.-F[0 _B ~> X ]0 ]0 )0 ).

  (* Lemma tmp_dkdkd  : forall (log : logic) (dat : data) (_B : obB dat) (_A : obA dat) (X : obA dat) (_W : obV log) (a : V(0 _W |- dat.-A[0 _A ~> X ]0 )0) ,
                       ( @eq (V(0 _W |- [0 dat.-F[0 _B ~> _A ]0 ~> dat.-F[0 _B ~> X ]0 ]0 )0)
                             (dat.-F[0 X ~> a ]1)  (@polyF _ dat _ _ _ (@IdenV _ _) X <o (a : V(0 _ |- A[0 _ ~> X ]0 )0)) ).
        reflexivity.
      Qed. *)
  End Ex_Notations4.
  Import Ex_Notations4.
  Notation "F[0 B ~> - ]1" := (_.-F[0 B ~> - ]1) (at level 25).
  Notation "F[0 X ~> a ]1" := (_ .-F[0 X ~> a ]1) (at level 25).

  Section Context4.
    Context {log : logic}.
    
    Class class (dat : @data log) :=
      Class {
          CongPolyA : forall (V : obV log), forall (B : obA dat), forall (A : obA dat),
                      forall (f f' : V(0 V |- A[0 B ~> A ]0 )0),
                        f' ~~ f -> forall X : obA dat, polyA f' X ~~ polyA f X;
          polyA_arrow :  forall (B : obA dat), forall (A : obA dat),
                         forall (V V' : obV log) (v : V(0 V' |- V )0),
                         forall (f : V(0 V |- A[0 B ~> A ]0 )0) (X : obA dat),
                           A[1 f <o v ~> X ]0
                            ~~ [1 v ~> A[0 B ~> X ]0 ]0 <o A[1 f ~> X ]0;
          polyF_arrow : forall (B : obB dat) (A : obA dat),
                        forall (V V' : obV log) (v : V(0 V' |- V )0),
                        forall (f : V(0 V |- F[0 B ~> A ]0 )0) (X : obA dat),
                          F[1 f <o v ~> X ]0
                           ~~ [1 v ~> F[0 B ~> X ]0 ]0 <o F[1 f ~> X ]0;
          polyF_morphism : forall (V : obV log) (B : obB dat),
                           forall (A : obA dat) (W : obV log) (A' : obA dat) (g : V(0 W |- A[0 A ~> A']0 )0),
                           forall (f : V(0 V |-F[0 B ~> A ]0 )0) (X : obA dat),
                             (* may use ( F[1 f ~> A']0 <o g ) because polyF_arrow is present .. may use ( DesIn( _ ) <o _ ) .. ConsIn *)
                             F[1 Des( [1 f ~> F[0 B ~> A' ]0 ]0 <o F[0 A' ~> g ]1 ) ~> X]0
                              ~~  ( DesIn( [0 W ~> F[1 f ~> X ]0 ]1 <o A[1 g ~> X ]0 )
                                    :  V(0 A[0 A' ~> X ]0 |- [0 (0 W & V )0 ~> F[0 B ~> X ]0 ]0 )0 );
          CongPolyF : forall (V : obV log) (B : obB dat) (A : obA dat),
                      forall (f f' : V(0 V |- F[0 B ~> A ]0 )0),
                        f' ~~ f -> forall X : obA dat, polyF f' X ~~ polyF f X;
          polyA_unitA : forall (A : obA dat), forall X : obA dat, (@IdenV _ (A[0 A ~> X ]0)) ~~ DesIdenObR( A[1 (@unitA _ dat A) ~> X ]0 );
          polyF_inputUnitA : forall (V : obV log) (B : obB dat) (A : obA dat),
                             forall (f : V(0 V |- F[0 B ~> A ]0 )0),
                               f ~~ DesIdenObL( (F[1 f ~> A ]0) <o (@unitA _ dat A) )
        }.

    Global Arguments CongPolyA {_ _} [_ _ _ _ _] _ _  .
    Global Arguments polyA_arrow {_ _} [_ _ _ _] _ _ _ .
    Global Arguments polyF_arrow {_ _} [_ _ _ _] _ _  _ .
    Global Arguments polyF_morphism {_ _} [_ _ _ _ _] _ _ _ .
    Global Arguments CongPolyF {_ _} [_ _ _ _ _] _ _ .
    Global Arguments polyA_unitA {_ _} _ _ .
    Global Arguments polyF_inputUnitA {_ _} [_ _ _] _  .

  (** (** possible but yoneda does not require polymorphism in B **)
      Parameter polyF_morphism_codomain : forall (dat : data) (V : obV log) (B : obB dat),
                             forall (A : obA dat) (W : obV log) (B' : obB dat) (b : V(0 W |- B[0 B' ~> B]0 )0),
                             forall (f : V(0 V |-F[0 B ~> A ]0 )0) (X : obA dat), (* use ( B[1 b ~> F|0 A ]0 <o f  ) because no polyB_arrow *)
                               F[1 Des( B[1 b ~> F|0 A ]0 <o f ) ~> X]0
                                ~~ ( DesIn( [0 V ~> B[1 b ~> F|0 X ]0 ]1 <o F[1 f ~> X ]0 )
                                        : V(0 A[0 A ~> X ]0 |- [0 (0 V & W )0 ~> F[0 B' ~> X ]0 ]0 )0 ) .
   **)
  End Context4.

  Coercion dat {log : logic} {dat : @data log} (ext : @class log dat) := dat.

  Section Context5.
    Variable (log : logic).

    (** printing for documentation
    Import LOGIC.Ex_Notations2.
    Check @polyF : forall (log : logic) (dat : data) (V : obV log) (B : obB dat) (A : obA dat),
                     log.-V(0 V |- dat.-F[0 B ~> A ]0 )0 ->
                     forall X : obA dat, log.-V(0 dat.-A[0 A ~> X ]0 |- log.-[0 V ~> dat.-F[0 B ~> X ]0 ]0 )0 . **)
    
    Structure functor :=
      Functor {
          data_of :> @data log;
          class_of :> @class _ data_of
        }.

    (* not critical, only for easy proofs without doing (class_of _) *)
    Global Existing Instance class_of. 
  End Context5.

  Section Context8.
    Context {log : logic}.
    Context {dat_ : @data log}.
    Context {func : @class _ dat_}.

    (** for polymorph functor, get this copy-paste same deduction as for polymorph category **)
    Lemma polyF_arrowIn : forall (B : obB func) (A : obA func),
                          forall (V W V' : obV log) (v : V(0 W |- [0 V' ~> V ]0 )0),
                          forall (f : V(0 V |- F[0 B ~> A ]0 )0) (X : obA func),
                            F[1 f <o (Des v) ~> X ]0
                             ~~ DesIn( V[1 v ~> F[0 B ~> X ]0 ]0 <o F[1 f ~> X ]0 ) .
    Proof.
      intros; eapply TransV; [ apply DesIn_Input | ].
      eapply TransV; [ | eapply polyF_arrow ]. 
      eapply CongCom; [ | eapply ReflV]; apply polyV_relV_polyV_relT. 
    Qed.

    Lemma polyF_natural : forall (V : obV log) (B : obB func) (A : obA func) (f : V(0 V |- F[0 B ~> A ]0)0),
                          forall (Y X : obA func),
                            ( [0 A[0 A ~> Y ]0 ~> F[1 f ~> X ]0 ]1
                              <o A[0 A ~> - ]1 Y X )
                              ~~ ( [1 F[1 f ~> Y ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
                                   <o ( V[0 V ~> - ]1 (F[0 B ~> Y ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 Y X ) .
    Proof.
      (* enough ( DesIn( _ ) ~~ DesIn( _ ) ) *)
      intros;  eapply TransV; [ eapply TransV | ]; [ apply ConsIn_DesIn | idtac | apply SymV, ConsIn_DesIn].
      apply CongConsIn.

      (* convert left hand side : outer polyF_morphism then inner polyF_arrow *)
      assert ( LHS1 : F[1 Des( [1 f ~> F[0 B ~> Y ]0 ]0 <o F[0 Y ~> (@IdenV _ (A[0 A ~> Y]0)) ]1 ) ~> X ]0
                       ~~ DesIn( [0 A[0 A ~> Y ]0 ~> F[1 f ~> X ]0 ]1 <o A[0 A ~> - ]1 Y X ) )
        by apply polyF_morphism.

      assert ( LHS2 : F[1 Des( F[1 (@IdenV _ (F[0 B ~> A ]0)) <o f ~> Y ]0 ) ~> X ]0
                       ~~ F[1 Des( [1 f ~> F[0 B ~> Y ]0 ]0 <o F[0 Y ~> (@IdenV _ (A[0 A ~> Y ]0)) ]1 ) ~> X ]0 )
        by ( apply CongPolyF, CongDes;  eapply TransV; [ eapply Cat2V | ]; eapply TransV; [ eapply Cat1RightV | ];
             apply polyF_arrow ).

      (* convert right hand side : outer polyV_relV_arrow then outer polyF_arrowIn which is inner form of polyF_arrow *)
      assert ( RHS1 : DesIn( ( V[1 (@IdenV _ (V[0 V ~> (F[0 B ~> Y ]0) ]0)) <o (F[1 f ~> Y ]0) ~> (F[0 B ~> X ]0) ]0 ) <o F[0 B ~> - ]1 Y X )
                           ~~ DesIn( [1 F[1 f ~> Y ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0 <o ( V[0 V ~> - ]1 (F[0 B ~> Y ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 Y X ) )
        by ( eapply TransV; [ eapply CongDesIn; eapply Cat2V | ];
             apply CongDesIn; apply CongCom; [ | apply ReflV];
             apply polyV_relV_arrow ).

      assert ( RHS2 : ( F[1 (@IdenV _ (F[0 B ~> Y ]0)) <o Des( (@IdenV _ (V[0 V ~> (F[0 B ~> Y ]0) ]0)) <o (F[1 f ~> Y ]0) ) ~> X ]0 )
                        ~~ DesIn( ( V[1 (@IdenV _ (V[0 V ~> (F[0 B ~> Y ]0) ]0)) <o (F[1 f ~> Y ]0) ~> (F[0 B ~> X ]0) ]0 ) <o F[0 B ~> - ]1 Y X ) )
        by apply polyF_arrowIn.

      (* clean right hand side *)
      eapply TransV; [ apply RHS1 | ] .  eapply TransV; [ apply RHS2 | ]. clear RHS2 RHS1.
      eapply TransV; [ apply CongPolyF, Cat1LeftV | ]. eapply TransV; [ apply CongPolyF, CongDes, Cat1LeftV | ].

      (* clean left hand side *)
      eapply TransV; [ | apply SymV, LHS1 ] .  eapply TransV; [ | apply SymV, LHS2 ]. clear LHS2 LHS1.
      eapply TransV; [ | apply CongPolyF, CongDes, CongPolyF, SymV, Cat1LeftV ].
      
      apply ReflV.
    Qed.

    Definition natural (V : obV log) (B : obB func) (A : obA func) (β : forall X : obA func, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0) :=
      forall (Y X : obA func),
        ( [0 A[0 A ~> Y ]0 ~> β X ]1
          <o A[0 A ~> - ]1 Y X )
          ~~ ( [1 β Y ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
               <o ( V[0 V ~> - ]1 (F[0 B ~> Y ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 Y X ) .

    (** for polymorph functor, get this copy-paste same deduction as for polymorph category **)
    Lemma natural_unitF_explicit : forall (V : obV log) (B : obB func) (A : obA func) (φ : forall X : obA func, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0),
                                     natural φ ->
                                     forall (X : obA func),
                                       DesIdenObR( [1 φ A <o (@unitA _ func A) ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
                                                   <o ( V[0 V ~> - ]1 (F[0 B ~> A ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 A X )
                                                 ~~ ( φ X ) .
    Proof.
      intros; eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ | apply ReflV]; apply consV10_functorial ].
      eapply TransV; [ | eapply CongDesIdenObR; eapply Cat2V ].
      eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ apply ReflV | ]; apply SymV, H ].
      eapply TransV; [ | eapply CongDesIdenObR; eapply SymV, Cat2V ].
      eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ | apply ReflV ]; apply SymV, consV11_bifunctorial ].
      eapply TransV; [ | eapply CongDesIdenObR; eapply Cat2V ].
      eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ apply ReflV | ]; apply SymV, polyA_arrow ].
      eapply TransV; [ | eapply CongDesIdenObR; eapply CongCom; [ apply ReflV | ]; apply CongPolyA, SymV, Cat1LeftV ].  
      eapply TransV; [ | eapply DesIdenObR_output].
      eapply TransV; [ | eapply CongCom; [ apply ReflV | ]; apply SymV, polyA_unitA ].
      apply SymV, Cat1RightV.
    Qed.
    
    (** for polymorph functor, get this copy-paste same deduction as for polymorph category **)
    Lemma natural_unitF : forall (V : obV log) (B : obB func) (A : obA func) (φ φ' : forall X : obA func, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0),
                            natural φ -> natural φ' ->
                            φ' A <o (@unitA _ func A)  ~~ φ A <o (@unitA _ func A) ->
                            forall X : obA func, φ' X ~~ φ X.
    Proof.
      intros; eapply TransV; [ apply natural_unitF_explicit; assumption |
                               eapply TransV; [ | apply SymV, natural_unitF_explicit; assumption ] ].
      apply CongDesIdenObR, CongCom; [ | apply ReflV ]; apply CongConsV10.
      assumption.
    Qed.

    (** for polymorph functor, get this copy-paste same deduction as for polymorph category **)
    Lemma YONEDA : forall (V : obV log) (B : obB func) (A : obA func) (φ φ' : forall X : obA func, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0),
                     natural φ ->
                     forall X : obA func, φ X ~~ F[1 DesIdenObL( (φ A) <o (@unitA _ func A) ) ~> X ]0 .
    Proof.
      intros; enough( φ A <o (@unitA _ func A) ~~ F[1 DesIdenObL( (φ A) <o (@unitA _ func A) ) ~> A ]0 <o (@unitA _ func A) ).
      apply natural_unitF; [ |  assumption | assumption ] .
      unfold natural; intros; apply polyF_natural.
      
      eapply TransV; [ apply SymV, ConsIdenObL_DesIdenObL | ].
      eapply TransV; [ | apply ConsIdenObL_DesIdenObL].
      apply CongConsIdenObL.
      eapply TransV; [ apply polyF_inputUnitA |  apply ReflV ].
    Qed.

  End Context8.
  
  Check fun log => fun ff : @functor log  =>  polyF_arrowIn (func:=ff).
End FUNCTOR.

Module FORM.
  Import FUNCTOR.
  Set Implicit Arguments.
  Unset  Strict Implicit.

  Section Context6.
    Context {log : logic}.

    Record data :=
      Data {
          obA : Type;
          polyA00 : obA -> obA -> obV log;
          polyA : forall (V : obV log), forall (A2 : obA), forall (A1 : obA),
                    V(0 V |- (polyA00 A2 A1) )0 ->
                    forall X : obA, V(0 (polyA00 A1 X)  |- [0 V ~> (polyA00 A2 X) ]0 )0;
          unitA : forall A : obA, V(0 I |- polyA00 A A )0;
        }.

    Coercion dataFun_of_dataCatForm (d : data)
    : @FUNCTOR.data log := {|
                            FUNCTOR.obA := obA d;
                            FUNCTOR.polyA00 := @polyA00 d;
                            FUNCTOR.polyA := @polyA d;
                            FUNCTOR.obB := obA d;
                            FUNCTOR.polyB00 := @polyA00 d;
                            FUNCTOR.polyB := @polyA d;
                            FUNCTOR.polyF0 := (@idT (obA d));
                            FUNCTOR.polyF := @polyA d;
                            FUNCTOR.unitA := @unitA d|}.

    Global Arguments dataFun_of_dataCatForm : simpl never.

  End Context6.
  
  Section Context7.
    Context {log : logic}.
    
    Class class (dat : data) :=
      Class {
          CongPolyA : forall (V : obV log), forall (B : FUNCTOR.obA dat), forall (A : FUNCTOR.obA dat),
                      forall (f f' : V(0 V |- A[0 B ~> A ]0 )0),
                        f' ~~ f -> forall X : FUNCTOR.obA dat, polyA f' X ~~ polyA f X;
          polyA_arrow :  forall (B : FUNCTOR.obA dat), forall (A : FUNCTOR.obA dat),
                         forall (V V' : obV log) (v : V(0 V' |- V )0),
                         forall (f : V(0 V |- A[0 B ~> A ]0 )0) (X :  FUNCTOR.obA dat),
                           A[1 f <o v ~> X ]0
                            ~~ [1 v ~> A[0 B ~> X ]0 ]0 <o A[1 f ~> X ]0;
          polyA_unitA : forall (A :  FUNCTOR.obA dat), forall X :  FUNCTOR.obA dat, (@IdenV _ (A[0 A ~> X ]0)) ~~ DesIdenObR( A[1 (@FUNCTOR.unitA _ dat A) ~> X ]0 );
        }.

    Global Arguments CongPolyA {_ _} [_ _ _ _ _] _ _  .
    Global Arguments polyA_arrow {_ _} [_ _ _ _] _ _ _ .
    Global Arguments polyA_unitA {_ _} _ _ .

  End Context7.

  Section Context8.
    Structure form (log : logic) :=
      Form {
          data_of :> @data log;
          class_of :> @class log (data_of)
        }.

    (* is this necessary?*)
    Global Existing Instance class_of.

    Coercion dataForm_of_dataFun {log} (dat : @FUNCTOR.data log)
    : @data log := {|
                    obA := FUNCTOR.obA dat;
                    polyA00 := @FUNCTOR.polyA00 _ dat;
                    polyA := @FUNCTOR.polyA _ dat;
                    unitA := @FUNCTOR.unitA _ dat |}.

    Global Arguments dataForm_of_dataFun : simpl never.

    Coercion classForm_of_classFun {log} (dat : @FUNCTOR.data log) (ext : @FUNCTOR.class log dat)
    : @FORM.class log dat :=
      @FORM.Class log dat (@FUNCTOR.CongPolyA log dat ext) (@FUNCTOR.polyA_arrow log dat ext)
                  (@FUNCTOR.polyA_unitA log dat ext).

    Global Arguments classForm_of_classFun : simpl never.

    Definition form_of_functor {log : logic} (func : @functor log)
    : @form log :=  {| data_of := func ; class_of := func |}.
    (** ?? Canonical Structure form_of_functor. ?? **)

    Goal forall log (func : @functor log), 
           FUNCTOR.data_of func = (@dataFun_of_dataCatForm log (@data_of log (@form_of_functor log func))) .
      Fail reflexivity.
      destruct func as [datfunc extfunc]. simpl. Set Printing All.  Show. Fail reflexivity.
      destruct datfunc. Unset Printing All.   compute. Fail reflexivity.
    Abort.

  End Context8.

  Notation form_of func := (@form_of_functor _ func).

  Export FUNCTOR.
End FORM.

Module CATEGORY.
  Export FORM.
  Set Implicit Arguments.
  Unset  Strict Implicit.

  Section Context8.
    Context {log : logic}.
    
    Class class (dat : FORM.data) :=
      Class {
          CongPolyA : forall (V : obV log), forall (B : FUNCTOR.obA dat), forall (A : FUNCTOR.obA dat),
                      forall (f f' : V(0 V |- A[0 B ~> A ]0 )0),
                        f' ~~ f -> forall X : FUNCTOR.obA dat, polyA f' X ~~ polyA f X;
          (* remember that polyV_relT_arrow , relate in particular the polyV_relT_constant to polyV_relT_identitary *)
          polyA_arrow :  forall (B : FUNCTOR.obA dat), forall (A : FUNCTOR.obA dat),
                         forall (V V' : obV log) (v : V(0 V' |- V )0),
                         forall (f : V(0 V |- A[0 B ~> A ]0 )0) (X :  FUNCTOR.obA dat),
                           A[1 f <o v ~> X ]0
                            ~~ [1 v ~> A[0 B ~> X ]0 ]0 <o A[1 f ~> X ]0;
          polyF_morphism : forall (V : obV log) (B :  FUNCTOR.obB dat),
                           forall (A :  FUNCTOR.obA dat) (W : obV log) (A' :  FUNCTOR.obA dat) (g : V(0 W |- A[0 A ~> A']0 )0),
                           forall (f : V(0 V |-F[0 B ~> A ]0 )0) (X : obA dat),
                             F[1 Des( [1 f ~> F[0 B ~> A' ]0 ]0 <o F[0 A' ~> g ]1 ) ~> X]0
                              ~~  DesIn( [0 W ~> F[1 f ~> X ]0 ]1 <o A[1 g ~> X ]0 );
          polyA_unitA : forall (A :  FUNCTOR.obA dat), forall X :  FUNCTOR.obA dat, (@IdenV _ (A[0 A ~> X ]0)) ~~ DesIdenObR( A[1 (@FUNCTOR.unitA _ dat A) ~> X ]0 );
          polyF_inputUnitA : forall (V : obV log), forall (B :  FUNCTOR.obA dat), forall (A :  FUNCTOR.obA dat),
                             forall (f : V(0 V |- A[0 B ~> A ]0 )0),
                               f  ~~ DesIdenObL( (A[1 f ~> A ]0) <o (@FUNCTOR.unitA _ dat A) );
        }.

    Global Arguments CongPolyA {_ _} [_ _ _ _ _] _ _  .
    Global Arguments polyA_arrow {_ _} [_ _ _ _] _ _ _ .
    Global Arguments polyF_morphism {_ _} [_ _ _ _ _] _ _ _ .
    Global Arguments polyA_unitA {_ _} _ _ .
    Global Arguments polyF_inputUnitA {_ _} [_ _ _] _ .

    Coercion classFun_of_classCat (dat : @FORM.data log) (ext : @class  dat)
    : @FUNCTOR.class log (dataFun_of_dataCatForm dat) := 
      {|
        FUNCTOR.CongPolyA := CongPolyA;
        FUNCTOR.polyA_arrow := polyA_arrow;
        FUNCTOR.polyF_arrow := polyA_arrow;
        FUNCTOR.polyF_morphism := polyF_morphism;
        FUNCTOR.CongPolyF := CongPolyA;
        FUNCTOR.polyA_unitA := polyA_unitA;
        FUNCTOR.polyF_inputUnitA := polyF_inputUnitA |}.

    Global Arguments classFun_of_classCat : simpl never.

  End Context8.

  Section Context9.
    Structure category (log : logic) :=
      Category {
          data_of :> @FORM.data log;
          class_of :> @class  log (data_of)
        }.

    (* is this necessary?*)
    Global Existing Instance class_of.

    Coercion functor_of_category {log : logic} (c : @category log)
    : @FUNCTOR.functor log :=  {| FUNCTOR.data_of := data_of c; FUNCTOR.class_of :=  class_of c |}.
    (* false ambiguity : new coercion produce same output as old coercion ; the new coercion will be used to coerce but also the notational hiddenness/implicitness of old coercion is kept for printing *)
    Canonical Structure functor_of_category.

    Goal forall (log : logic) (func : @category log),
           FUNCTOR.data_of func = (@dataFun_of_dataCatForm log (@FORM.data_of log (@form_of_functor log func))) .
      reflexivity.
    Qed.
    
    Coercion category_of_logic (log : logic) : @category log :=
      @Category log _
                (@Class log
                        {|
                          FORM.obA := obV log;
                          FORM.polyA00 := @consV00 log;
                          FORM.polyA := @polyV_relV log;
                          FORM.unitA := @unitV log |} (@CongPolyV log) (@polyV_relV_arrow log)
                        (@polyV_relV_morphism log) (@polyV_relV_unitV log)
                        (@polyV_relV_inputUnitV log)) .

    Canonical Structure category_of_logic.
  End Context9.
  Export FUNCTOR.
End CATEGORY.

Module FUNCTORTOCAT.
  Export CATEGORY.
  Import FUNCTOR.Ex_Notations4.
  Set Implicit Arguments.
  Unset  Strict Implicit.

  Section Context.
    Context {log : logic} (from : @form log) (to : @category log).
    
    Record data :=
      Data {
          polyF0 : obA from -> obA to;
          polyF :   forall {V : obV log}{B : obA to} {A : obA from},
                      V(0 V |- to .-A[0 B ~> polyF0 A ]0 )0 ->
                      forall X : obA from,
                        V(0 from .-A[0 A ~> X ]0 |- [0V ~> to .-A[0 B ~> polyF0 X ]0 ]0 )0;
        }.

    Coercion dataFun_of_dataFuntoCat (d : data)
    : @FUNCTOR.data log :=  {|
                            FUNCTOR.obA := @obA _ from;
                            FUNCTOR.polyA00 := @polyA00 _ from;
                            FUNCTOR.polyA := @polyA _ from;
                            FUNCTOR.obB := @obA _ to;
                            FUNCTOR.polyB00 := @polyA00 _ to;
                            FUNCTOR.polyB := @polyA _ to;
                            FUNCTOR.polyF0 := polyF0 d;
                            FUNCTOR.polyF := @polyF d;
                            FUNCTOR.unitA := @unitA _ from |}.

    Global Arguments dataFun_of_dataFuntoCat : simpl never. (** really useful with cbn **)

  End Context.

  Section Context2.
    Context {log : logic} {from : @form log} {to : @category log}.

    Class class (dat : @data log from to) :=
      Class {
          polyF_arrow :    forall {B : obA to} {A : obA from} {V V' : obV log} 
                             (v : V(0 V' |- V )0) (f : V(0 V |- to .-A[0 B ~> polyF0 dat A ]0 )0)
                             (X : obA from),
                             dat.-F[1  (f <o v) ~> X ]0 ~~
                                [1v ~> to .-A[0 B ~> dat.-F|0 X ]0 ]0 <o dat.-F[1 f ~> X ]0 ;
          polyF_morphism :    forall (V : obV log) (B : obA to) (A : obA from) 
                                (W : obV log) (A' : obA from) (g : V(0 W |- from .-A[0 A ~> A' ]0 )0)
                                (f : V(0 V |- to .-A[0 B ~> polyF0 dat A ]0 )0) (X : obA from),
                                dat.-F[1 (Des ([1f ~> to .-A[0 B ~> dat.-F|0 A' ]0 ]0 <o dat.-F[1 1 ~> A' ]0 <o g)) ~> X ]0 ~~
                                   DesIn ([0W ~> dat.-F[1 f ~> X ]0 ]1 <o from .-A[1 g ~> X ]0) ;
          CongPolyF :    forall (V : obV log) (B : obA to) (A : obA from)
                           (f f' : V(0 V |- to .-A[0 B ~> dat.-F|0 A ]0 )0),
                           f' ~~ f -> forall X : obA from, dat.-F[1 f' ~> X ]0 ~~ dat.-F[1 f ~> X ]0 ;
          polyF_inputUnitA :    forall (V : obV log) (B : obA to) (A : obA from)
                                  (f : V(0 V |- to .-A[0 B ~> dat.-F|0 A ]0 )0),
                                  f ~~ DesIdenObL (dat.-F[1 f ~> A ]0 <o (from) .-uA)
        }.

    Global Arguments polyF_arrow {_ _} [_ _ _ _] _ _  _ .
    Global Arguments polyF_morphism {_ _} [_ _ _ _ _] _ _ _ .
    Global Arguments CongPolyF {_ _} [_ _ _ _ _] _ _ .
    Global Arguments polyF_inputUnitA {_ _} [_ _ _] _  .

    Coercion classFun_of_classFuntoCat (dat : @data log from to) (ext : @class dat)  :  @FUNCTOR.class log dat :=
      FUNCTOR.Class (dat:=dat) (@FORM.CongPolyA _ _ from) (@FORM.polyA_arrow _ _ from) (@polyF_arrow dat ext)
                    (@polyF_morphism _ ext) (@CongPolyF _ ext) (@FORM.polyA_unitA _ _ from)
                    (@polyF_inputUnitA _ ext).

    Global Arguments classFun_of_classFuntoCat : simpl never.

  End Context2.

  Section Context3.
    Context {log : logic} (from : @form log) (to : @category log).

    Structure functorToCat :=
      FunctorToCat {
          data_of :> @data log from to;
          class_of :> @class _ _ _ (data_of)
        }.

    (* is this necessary?*)
    Global Existing Instance class_of.

    Coercion functor_of_functorToCat (func : functorToCat)
    : @FUNCTOR.functor log :=  {| FUNCTOR.data_of := data_of func; FUNCTOR.class_of := class_of func |}.
    (* false ambiguity : new coercion produce same output as old coercion ; the new coercion will be used to coerce but also the notational hiddenness/implicitness of old coercion is kept for printing *)
    Canonical Structure functor_of_functorToCat.

    Definition polyF_unitB {func : functorToCat} : forall (A : obA from),
                                                   forall X : obA from, V(0 from.-A[0 A ~> X ]0  |- to.-A[0 func.-F|0 A ~> func.-F|0 X ]0 )0.
      intros.
      apply DesIdenObR.
      eapply polyF.
      apply (@unitA _ to).
      Show Proof.
    (* (fun (func : functorToCat) (A X : obA from) =>
 DesIdenObR (polyF (d:=func) (to) .-uA X)) *)
    Defined.

  End Context3.
  
  Module Ex_Notations6.
    Notation "dat .-F|1" := (@polyF_unitB _ _ _ dat) (at level 0, format "dat .-F|1").
  End Ex_Notations6.
  Import Ex_Notations6.
  Notation "F|1" := (_ .-F|1) (at level 0).

  Section Context4.
    Context {log : logic} (catA : form log) (catB : category log) (funF : functorToCat catA catB) (B : obB catB).

    (** functors are very primitive therefore no reason for this sequencing lemma to hold,         
but later polyF_identitary_rel_polyF_unitB do hold    for alone functorToCat_of_metafunctor    or   for funComp composition of two functors  ,
also later with the polymorphism in B assumption and the B is category (polyB_inputUnitB) assumption then this lemma hold **)
    Lemma polyF_identitary_rel_polyF_unitB_ABORT : forall (A X : obA catA),
                                                     (catB.-F[0 B ~> - ]1) (funF.-F|0 A) (funF.-F|0 X) <o funF.-F|1 A X ~~
                                                                                                                    (funF.-F[0 B ~> - ]1) A X  .
    Proof. (*intros.
        Check  (funF.-F[0 B ~> - ]1) A X . Check F|1 A X. Check  (catB.-F[0 B ~> - ]1).
        Set Printing Coercions. intros. Show.
        intros. simpl.   simpl. Unset Printing Implicit Defensive. Show. unfold polyF_unitB. simpl. 
        eapply TransV; [| eapply SymV, DesIdenObR_output ].
        
        unfold polyF_IdenV.
        eapply CongDesIdenObR.
         apply DesIdenObR_output.
      Qed.*) 
    Abort.

  End Context4.

  Section Context5.   
    (*    Import Ex_Notations.*)
    Import LOGIC.Ex_Notations3.
    Import FUNCTOR.Ex_Notations4.
    Variable (log : logic).
    Variable (pf : @convV log = fun V1 V2 => (eq : V(0 V1 |- V2 )0 -> V(0 V1 |- V2 )0 -> Prop) ).

    Eval unfold polyT_relT_identitary, idT in fun a b => a <<o b.
    Eval unfold polyT_relT_constant, cstT in fun b a => b o>> a.
    (*BUG fix *)
    Local Notation "a <<o b" := ((T(1 (fun h : _ => h) |- _ )0) a b) (at level 33, right associativity).
    Local Notation "b o>> a" := ( (T(1 fun _ : unit => b |- _ )0) a tt) (at level 33, right associativity).
    (* ATTEMPT   Notation "a <o b" := (@polyV_relT_identitary _ _ _ _ a b) (at level 33, right associativity).
    Notation "b o> a" := (@polyV_relT_constant _ _ _ b _ a) (at level 33, right associativity).*)
    (* ATTEMPT Local Notation "b o> a" := (b o>_> a) (at level 33, right associativity).
    Local Notation "a <o b" := (a <_<o b) (at level 33, right associativity).*)
    Local Notation "b o>' a" := (b o> _ > a) (at level 33, right associativity). Print Grammar constr.
    Local Notation "a <o' b" := (a < _ <o b) (at level 33, right associativity).

    Definition category_relT_of_logic : @category logT.
      unshelve econstructor.
      - unshelve econstructor.
        + eapply (@obV log).
        + eapply (@polyV_relT00 log).
        + eapply (@polyV_relT log).
        + eapply (@unitV_relT log).
      - unshelve econstructor.
        + simpl. intros * -> . reflexivity.
        +  simpl. generalize (@polyV_relT_arrow log log).
           intros H_polyV_relT_arrow; intros.  erewrite  !pf in *.
           do 2 (apply functional_extensionality_T; intros).
           apply H_polyV_relT_arrow; reflexivity.
        + simpl. generalize (@polyV_relT_morphism log log).
          intros H_polyV_relT_morphism; intros.  erewrite  !pf in *.
          do 2 (apply functional_extensionality_T; intros).
          apply H_polyV_relT_morphism.
        + simpl. generalize (@polyV_relT_unitV log log).
          intros H_polyV_relT_unitV; intros.  erewrite  !pf in *.
          do 1 (apply functional_extensionality_T; intros). 
          eapply H_polyV_relT_unitV; reflexivity.
        + simpl. generalize (@polyV_relT_inputUnitV log log).
          intros H_polyV_relT_inputUnitV; intros.  erewrite  !pf in *.
          do 1 (apply functional_extensionality_T; intros). 
          eapply H_polyV_relT_inputUnitV; reflexivity.
    Qed.

  End Context5.
  Export FUNCTOR.
End FUNCTORTOCAT.

Module TRANSFORMATION.
  Import FUNCTORTOCAT.
  Import FUNCTOR.Ex_Notations4.
  Set Implicit Arguments.
  Unset Strict Implicit.

  Section Context.
    Context {log : logic} {catA : @form log} {catB : category log}.
    Variable (funF : functorToCat catA catB).
    Variable (funG : functorToCat catA catB).

    Record data :=
      Data {
          polyβ : forall (V : obV log) (B : obA catB) (A : obA catA),
                    V(0 V |- funF.-F[0 B ~> A ]0 )0 ->
                    V(0 V |- funG.-F[0 B ~> A ]0 )0
        }.
  End Context.

  Module Ex_Notations.
    Notation "dat .-β|1 f" := (@polyβ _ _ _ _ _ dat _ _ _ f) (at level 5, right associativity, format "dat .-β|1  f").
  End Ex_Notations.
  Import Ex_Notations.
  Notation "β|1 f" := (_.-β|1 f) (at level 5, right associativity).

  Section Context2.
    Context {log : logic} {catA : form log} {catB : category log}.
    Variable (funF : functorToCat catA catB).
    Variable (funG : functorToCat catA catB).
    

    Class class {dat : data funF funG} :=
      Class {
          polyβ_arrow : forall (B : obA catB) (A : obA catA),
                        forall (V V' : obV log) (v : V(0 V' |- V )0),
                        forall (f : V(0 V |- funF.-F[0 B ~> A ]0 )0),
                          dat.-β|1 (f <o v)
                                   ~~ dat.-β|1 f <o v;
          (** written here : (inner modification) ~~ (outer modification)**)
          polyβ_morphism : forall (V : obV log) (B : obA catB),
                           forall (A : obA catA) (W : obV log) (A' : obA catA) (a : V(0 W |- A[0 A ~> A']0 )0),
                           forall (f : V(0 V |- funF.-F[0 B ~> A ]0 )0),
                             dat.-β|1 (Des( [1 f ~> funF.-F[0 B ~> A' ]0 ]0 <o funF.-F[0 A' ~> a ]1 ))
                                      ~~ (Des( [1 dat.-β|1 f ~> funG.-F[0 B ~> A' ]0 ]0 <o funG.-F[0 A' ~> a ]1 )) ;
          polyβ_morphism_codomain : forall (V : obV log),
                                    forall (B : obA catB) (W : obV log) (B' : obA catB) (b : V(0 W |- catB.-A[0 B' ~> B]0 )0),
                                    forall (A : obA catA),
                                    forall (f : V(0 V |-funF.-F[0 B ~> A ]0 )0),
                                      dat.-β|1 (Des( catB.-A[1 b ~> funF.-F|0 A ]0 <o f ))
                                               ~~  Des( catB.-A[1 b ~> funG.-F|0 A ]0 <o dat.-β|1 f );
        }.

    Global Arguments polyβ_arrow {_ _} [_ _ _ _] _ _ .
    Global Arguments polyβ_morphism {_ _} [_ _ _ _ _] _ _ .
    Global Arguments polyβ_morphism_codomain {_ _} [_ _ _ _ _] _ _ .
    
    Structure transformation :=
      Transf {
          data_of :> data funF funG;
          class_of :> @class (data_of)
        }.

    (* is this necessary?*)
    Global Existing Instance class_of.

  End Context2.
End TRANSFORMATION.

Module METAFUNCTOR.
  Export FUNCTORTOCAT.
  Set Implicit Arguments.
  Unset Strict Implicit.

  Section Context.
    Context {log : logic} (from : form log).

    Record data :=
      Data {
          metaF0 : obA from -> obV log;
          metaF : forall (V : obV log) (A : obA from),
                    V(0 V |- (metaF0 A) )0 ->
                    forall X : obA from, V(0 (polyA00 A X)  |- [0 V ~> (metaF0 X) ]0 )0;
        }.
    
  End Context.

  Delimit Scope meta with meta.
  Local Open Scope meta.
  Module Ex_Notations.
    (** no scoping necessary for duplicate because definitionally same with poly for same notations     dat .-F|0 A   ,    dat .-F[0 B ~> A ]0, 
      else extra notation  dat .-F[1M b ~> X ]0 **)
    Notation "dat .-F|0 A" := (@metaF0 _ _ dat A) (at level 4, right associativity) : meta.
    Notation "dat .-F[0 B ~> A ]0" := (V[0 B ~> dat .-F|0 A ]0) (at level 25) : meta.
    Notation "dat .-F[1M b ~> X ]0" := (@metaF _ _ dat _ _ b X) (at level 25).
  End Ex_Notations.
  Import Ex_Notations.
  Notation "F|0 A" := (_ .-F|0 A) (at level 4, right associativity) : meta.
  Notation "F[0 B ~> A ]0" := (_ .-F[0 B ~> A ]0) (at level 25) : meta.
  Notation "F[1M b ~> X ]0" := (_ .-F[1M b ~> X ]0) (at level 25).
  
  Section Context2.
    Context {log : logic}  (from : form log).
    Context {dat : @data log from}.

    Definition metaF_IdenV : forall A X : obA from, V(0 A[0 A ~> X ]0 |- [0 F|0 A ~> F|0 X ]0 )0
      :=  (fun A X => @metaF _ _ dat _ A (@IdenV _ _) X).

  End Context2.

  Module Ex_Notations2.
    Export Ex_Notations.
    Notation "dat .-F||1" := (@metaF_IdenV _ _ dat _ _) (at level 0).
  End Ex_Notations2.
  Import Ex_Notations2.
  Notation "F||1" := (_ .-F||1) (at level 0).

  Section Context3.
    Context {log : logic} {from : form log}.
    
    Class class {dat : @data log from} :=
      Class {
          metaF_arrow : forall (A : obA from),
                        forall (V V' : obV log) (v : V(0 V' |- V )0),
                        forall (f : V(0 V |- dat.-F|0 A )0) (X : obA from),
                          F[1M f <o v ~> X ]0
                           ~~ [1 v ~> F|0 X ]0 <o F[1M f ~> X ]0 ;
          metaF_morphism : forall (V : obV log),
                           forall (A : obA from) (W : obV log) (A' : obA from) (g : V(0 W |- A[0 A ~> A']0 )0),
                           forall (f : V(0 V |-F|0 A )0) (X : obA from),
                             F[1M Des( [1 f ~> F|0 A' ]0 <o (dat.-F||1 <o g) ) ~> X]0
                              ~~  DesIn( [0 W ~> F[1M f ~> X ]0 ]1 <o A[1 g ~> X ]0) ;
          CongMetaF : forall (V : obV log)(A : obA from),
                      forall (f f' : V(0 V |- dat.-F|0 A )0),
                        f' ~~ f -> forall X : obA from, F[1M f' ~> X ]0 ~~ F[1M f ~> X ]0 ;
          metaF_inputUnitA : forall (V : obV log) (A : obA from),
                             forall (f : V(0 V |- dat.-F|0 A )0),
                               f ~~ DesIdenObL( (F[1M f ~> A ]0) <o (@unitA _ from A) ) ;
        }.

    Global Arguments metaF_arrow {_ _} [_ _ _] _ _  _ .
    Global Arguments metaF_morphism {_ _} [_ _ _ _] _ _ _ .
    Global Arguments CongMetaF {_ _} [_ _ _ _] _ _  .
    Global Arguments metaF_inputUnitA {_ _} [_ _] _  .

  End Context3.
  Section Context4.
    Context {log : logic} (from : form log).

    Structure metafunctor :=
      Metafunctor {
          data_of :> @data log from;
          class_of :> @class log from data_of
        }.

    (* not critical, only for easy proofs without doing (class_of _) *)
    Global Existing Instance class_of. 
    
    Coercion dataFunToCat_of_metafunctor  (dat : @metafunctor)
    : @FUNCTORTOCAT.data log from (CATEGORY.category_of_logic log) :=
      @FUNCTORTOCAT.Data log
                         from (CATEGORY.category_of_logic log)
                         (@metaF0 log from dat)
                         (fun (V B : obV log) (A : obA from) (b : V(0 V |- F[0 B ~> A ]0 )0)
                            (X : obA from) => ConsIn (F[1M Des b ~> X ]0)).

    Global Arguments dataFunToCat_of_metafunctor : simpl never.

    Lemma poly_of_metaF_arrow:
      forall (dat : data from)(ext : @class log from dat) (B : obV log) (A : obA from) 
        (V V' : obV log) (v : V(0 V' |- V )0) (f : V(0 V |- dat.-F[0 B ~> A ]0 )0)
        (X : obA from),
        ConsIn (F[1M Des (f <o v) ~> X ]0) ~~
               [1 v ~> F[0 B ~> X ]0 ]0 <o ConsIn (F[1M Des f ~> X ]0).
    Proof.
      intros; eapply TransV; [| eapply CongConsIn, CongMetaF, Des_Input ].
      eapply TransV; [| eapply CongConsIn, metaF_arrow ].
      apply ConsIn_Output.  
    Qed.

    Lemma poly_of_metaF_morphism:
      forall dat : data from, @class log from dat ->
                         forall (V B : obV log) (A : obA from) (W : obV log) 
                           (A' : obA from) (g : V(0 W |- A[0 A ~> A' ]0 )0)
                           (f : V(0 V |- dat.-F[0 B ~> A ]0 )0) (X : obA from),
                           ConsIn
                             (F[1M Des
                                   (Des
                                      ([1 f ~> F[0 B ~> A' ]0 ]0 <o
                                                                    ConsIn (F[1M Des 1 ~> A' ]0) <o g)) ~> X ]0) ~~
                             DesIn ([0 W ~> ConsIn (F[1M Des f ~> X ]0) ]1 <o A[1 g ~> X ]0).
    Proof.
      (* enough (  [1Assoc ~> P|0 X ]0 <o DesIn ( _ ) ~~  [1Assoc ~> P|0 X ]0 <o DesIn ( _ ) ) *)
      intros;  eapply TransV; [ eapply TransV | ]; [ apply ConsIn_DesIn | idtac | apply SymV, ConsIn_DesIn].
      apply CongConsIn, Assoc_Iso.

      (** LHS **)
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply DesIn_ConsIn].
      eapply TransV; [| eapply SymV, metaF_arrow ].
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply CongConsIn, CongMetaF, Cat1LeftV | eapply ReflV]  ] | eapply ReflV ] ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply CongConsIn, metaF_arrow | eapply ReflV]  ] | eapply ReflV ] ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply ConsIn_Input | eapply ReflV]  ] | eapply ReflV ] ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply Cat2V  ] | eapply ReflV ] ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply CongDes, CongDes, SymV, Cat2V  | eapply ReflV ] ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply CongDes, Des_Input  | eapply ReflV ] ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply Des_Input  | eapply ReflV ] ] .
      eapply TransV; [| eapply CongMetaF, Cat2V ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply ReflV | eapply SymV, Assoc_nat0 ] ] .
      eapply TransV; [| eapply CongMetaF, SymV, Cat2V ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [ eapply SymV, Des_consV10_functorial  | eapply ReflV] ] .
      eapply TransV; [| eapply CongMetaF, CongCom; [|eapply ReflV]; eapply CongDes, CongConsV10, CongDes, SymV, Cat1LeftV ] .
      eapply TransV; [| eapply CongMetaF, SymV, Des_Input ] .

      (** RHS **)
      (*extraline*)         eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongDesIn; eapply DesIn_Input |].
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply DesIn_Input |].
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongDesIn, CongConsV01, CongConsIn, CongMetaF, SymV, Cat1LeftV |].
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongDesIn, CongConsV01, CongConsIn, SymV, metaF_arrow  |].
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongDesIn, CongConsV01, SymV, ConsIn_Input  |].
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongDesIn, SymV, consV01_functorial  |].
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, DesIn_Input  |].
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply DesIn_Input  |].
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply SymV, Cat2V  |].
      eapply TransV; [ eapply Cat2V  |].
      eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply Assoc_DesIn_DesIn  |].
      eapply TransV; [ eapply Cat2V  |].
      eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply SymV, DesIn_Input  |].
      eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongDesIn, consV01_functorial  |].
      eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongConsV01, metaF_arrow  |].
      eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongConsV01, CongMetaF, Cat1LeftV  |].
      (*extraline*)         eapply TransV; [eapply SymV, DesIn_Input |].

      eapply metaF_morphism.
    Qed.            
    
    Lemma Cong_poly_of_metaF:
      forall dat : data from,
        @class log from dat ->
        forall (V B : obV log) (A : obA from) (f f' : V(0 V |- dat.-F[0 B ~> A ]0 )0),
          f' ~~ f ->
          forall X : obA from,
            ConsIn (F[1M Des f' ~> X ]0) ~~ ConsIn (F[1M Des f ~> X ]0).
    Proof.
      intros. eapply CongConsIn, CongMetaF, CongDes. assumption.
    Qed.

    Lemma poly_of_metaF_inputUnitA:
      forall dat : data from,
        @class log from dat ->
        forall (V B : obV log) (A : obA from) (f : V(0 V |- dat.-F[0 B ~> A ]0 )0),
          f ~~ DesIdenObL (ConsIn (F[1M Des f ~> A ]0) <o uA).
    Proof.
      intros ? ext; intros; eapply TransV; [eapply Cons_Des|]. eapply TransV; [|eapply SymV, Cons_Des].
      eapply CongCons.
      eapply TransV; [eapply CongDes, CongDesIdenObL, ConsIn_Input|].
      eapply TransV; [eapply Des_ConsIn|].
      eapply (@metaF_inputUnitA _ _ _ ext).
    Qed.

    Coercion classFunToCat_of_metafunctor (func : @metafunctor)
    : @FUNCTORTOCAT.class log from (CATEGORY.category_of_logic log) (dataFunToCat_of_metafunctor func) :=
      @FUNCTORTOCAT.Class log
                          from (CATEGORY.category_of_logic log)
                          (dataFunToCat_of_metafunctor func)
                          (poly_of_metaF_arrow func)
                          (poly_of_metaF_morphism func) (Cong_poly_of_metaF func)  (poly_of_metaF_inputUnitA func).
    
    Coercion functorToCat_of_metafunctor (func : @metafunctor)
    : @FUNCTORTOCAT.functorToCat log from (CATEGORY.category_of_logic log) :=  {| FUNCTORTOCAT.data_of :=  func; FUNCTORTOCAT.class_of :=  func |}.
    Canonical Structure functorToCat_of_metafunctor.
    
    (* poly_of_metaF_unitV_metaF_IdenV
     : forall (func : metafunctor) (A X : METAFUNCTOR.obA func),
       F|1 A X ~~ F||1 *)  (* solve difference in notation? *)
    Lemma poly_of_metaF_unitV_metaF_IdenV (func : metafunctor): forall A X : obA from, 
                                                                  @FUNCTORTOCAT.polyF_unitB log from (CATEGORY.category_of_logic log) func A X ~~ @metaF_IdenV _ _ func A X .
    Proof.
      intros.
      unfold metaF_IdenV.
      eapply TransV; cycle 1.
      eapply CongDesIdenObR, CongConsIn, CongMetaF, Cat1LeftV .
      eapply TransV; [| eapply CongDesIdenObR, CongConsIn, metaF_arrow ].
      eapply TransV; [| eapply CongDesIdenObR, ConsIn_Input ].
      eapply TransV; [| eapply DesIdenObR_Input ].
      eapply TransV; [| eapply CongCom; [eapply SymV, consV10_DesIdenObL | eapply ReflV] ].
      eapply TransV; [| eapply CongCom; [ eapply CongConsV10, SymV, unitV_IdenV  | eapply ReflV] ].
      eapply TransV; [| eapply CongCom; [ eapply SymV, consV10_functorial_fun1  | eapply ReflV] ].
      eapply SymV, Cat1LeftV.
    Qed.
    
  End Context4.

  Import FUNCTOR.Ex_Notations4.
  Import FUNCTORTOCAT.Ex_Notations6.
  Section Context6.
    Context {log : logic} (func : functor log)  (B : obB func) .

    Definition dataMetafun_of_functor_at : @METAFUNCTOR.data log (FORM.form_of_functor func)  := {|
                                                                                                  metaF0 := fun A : FUNCTOR.obA (form_of_functor func) => func.-F[0 B ~> A ]0;
                                                                                                  metaF := (fun (V : obV log) (A : obA (form_of_functor func)) (f : V(0 V |- func.-F[0 B ~> A ]0 )0) (X : obA (form_of_functor func)) => func.-F[1 f ~> X ]0  (* @polyF log func V B A f X *)  ) |}.

    (* is this necessary ?*)
    Global Arguments dataMetafun_of_functor_at : simpl never.

    Definition classMetafun_of_functor_at : @METAFUNCTOR.class log (FORM.form_of_functor func) dataMetafun_of_functor_at  :=
      (@Class log (@form_of_functor log func) dataMetafun_of_functor_at
              (fun A V V' v f X => @polyF_arrow _ _ func B A V V' v f X)
              (fun V A W A' g f X => @polyF_morphism _ _ func V B A W A' g f X)
              (fun V A f f' H X =>  @CongPolyF _ _ func V B A f f' H X)
              (fun V A f =>  @polyF_inputUnitA _ _ func V B A f)) .

    (* is this necessary **)
    Global Arguments classMetafun_of_functor_at : simpl never.

  End Context6.

  Definition metafunctor_of_functor_at {log : logic} (func : functor log)  (B : @FUNCTOR.obB log func)
  : @metafunctor log (form_of_functor func) :=  {| data_of := (@dataMetafun_of_functor_at log func B) ; class_of := (@classMetafun_of_functor_at log func B) |}.
  (**    Coercion metafunctor_of_functor_at : FUNCTOR.obB >-> metafunctor. (* coercion ? *) **)
  Canonical Structure metafunctor_of_functor_at.

  Notation meta_of func B := (@metafunctor_of_functor_at _ func B).
  
  Lemma meta_of_polyF_at_identitary_rel_polyF_identitary {log : logic} (func : functor log) (B : @obB log func)
  : forall A X : obA func, (@metafunctor_of_functor_at log func B).-F||1= func.-F[0 B ~> - ]1 A X .
  Proof.
    reflexivity.
  Qed.

  Lemma meta_of_polyF_at_identitary_rel_polyF_identitary' {log : logic} (func : functor log) (B : @obB log func)
  : forall A X : obA func, (@metafunctor_of_functor_at log func B).-F||1 ~~ func.-F[0 B ~> - ]1 A X .
  Proof.
    intros. apply ReflV.
  Qed.
  
  Section Context8.
    Context {log : logic} (from : form log) (func : @metafunctor log from).
    Let funF : functorToCat from (category_of_logic log) := functorToCat_of_metafunctor func.
    Variable (B : obB (category_of_logic log)).

    Local Unset Printing Implicit Defensive.
    Lemma polyF_identitary_rel_polyF_unitB_metaFunc : forall (A X : obA from),
                                                        ( (category_of_logic log).-F[0 B ~> - ]1) (funF.-F|0 A) (funF.-F|0 X) <o funF.-F|1 A X ~~
                                                                                                                                           (funF.-F[0 B ~> - ]1) A X  .
    Proof.
      intros. simpl. unfold polyV_relV. unfold polyF_unitB. simpl.
      eapply TransV; [| eapply SymV, ConsIn_Input ].
      eapply CongConsIn.

      (* LHS *)
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDesIdenObR, CongConsIn, CongMetaF, Cat1LeftV ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDesIdenObR, CongConsIn, metaF_arrow ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDesIdenObR, ConsIn_Input ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply DesIdenObR_Input ].
      eapply TransV; [| eapply SymV, Cat2V ].

      (* RHS *)
      eapply TransV; [eapply CongMetaF, SymV, Cat1LeftV  |].
      eapply TransV; [eapply SymV, metaF_arrow  |].

      (* pure logic *)
      eapply CongCom; [| eapply ReflV].
      eapply TransV; [ eapply SymV, Cat1RightV |]. eapply CongCom; [eapply ReflV|].
      eapply TransV; [| eapply SymV, DesIdenObR_DesIdenObL].
      eapply TransV; [| eapply CongConsV10, SymV, unitV_IdenV  ].
      eapply SymV, consV10_functorial_fun1.
    Qed.
  End Context8.

  Export FUNCTOR.
End METAFUNCTOR.

Module METATRANSFORMATION.
  Import TRANSFORMATION.
  Export METAFUNCTOR.
  Import FUNCTOR.Ex_Notations4.
  Import TRANSFORMATION.Ex_Notations.
  Import METAFUNCTOR.Ex_Notations2.
  Set Implicit Arguments.
  Unset Strict Implicit.

  Section Context.
    Context {log : logic} {catA : form log}.
    Variable (funF : metafunctor catA).
    Variable (funG : metafunctor catA).

    Record data :=
      Data {
          metaβ : forall (A : obA catA),
                    V(0 funF.-F|0 A |- funG.-F|0 A )0
        }.

  End Context.
  
  Module Ex_Notations.
    Notation "dat .-β||0 A" := (@metaβ _ _ _ _ dat A) (at level 4, right associativity, format "dat .-β||0  A").
  End Ex_Notations.
  Import Ex_Notations.
  Notation "β||0 A" := (_ .-β||0 A) (at level 4, right associativity).

  Section Context2.
    Context {log : logic} {catA : form log}.
    Variable (funF : metafunctor catA).
    Variable (funG : metafunctor catA).  

    Class class (dat : data funF funG) :=
      Class {
          metaβ_morphism : forall (A : obA catA)  (A' : obA catA),
                             [0 funF.-F|0 A ~>  dat.-β||0 A' ]1 <o funF.-F||1
                                                                  ~~ [1 dat.-β||0 A ~> funG.-F|0 A' ]0 <o funG.-F||1;
        }.

    Global Arguments metaβ_morphism {_ _} _ _ .
    
    Structure metatransformation :=
      Metatransf {
          data_of :> data funF funG;
          class_of :> @class (data_of)
        }.

    (* is this necessary?*)
    Global Existing Instance class_of.

    Coercion dataTransformation_of_dataMetatransformation log catA funF funG (dat : @data log catA funF funG)
    : @TRANSFORMATION.data log catA (CATEGORY.category_of_logic log) funF funG :=
      @TRANSFORMATION.Data log catA (CATEGORY.category_of_logic log) funF funG
                           ( fun (V B : obV log) (A : obA catA) (b : V(0 V |- funF.-F[0 B ~> A ]0 )0) =>
                               Cons (dat.-β||0 A <o Des b) ).

    Global Arguments dataTransformation_of_dataMetatransformation : simpl never.

    (** lemmas **)
    Lemma  poly_of_metaβ_arrow:
      forall dat : data funF funG,
        @class dat ->
        forall (B : obA log) (A : obA catA) (V V' : obV log) 
          (v : V(0 V' |- V )0) (f : V(0 V |- funF.-F[0 B ~> A ]0 )0),
          dat.-β|1 (f <o v) ~~ dat.-β|1 f <o v.
    Proof.
      intros; eapply TransV; [ eapply Cons_Input  |] .
      eapply TransV; [ eapply CongCons; eapply SymV, Cat2V  |] .
      eapply TransV; [ eapply CongCons; eapply CongCom; [ eapply ReflV |  eapply Des_Input  ] |] .
      eapply ReflV.
    Qed.

    Lemma poly_of_metaβ_morphism:
      forall dat : data funF funG,
        @class dat ->
        forall (V : obV log) (B : obA log) (A : obA catA) 
          (W : obV log) (A' : obA catA) (a : V(0 W |- catA .-A[0 A ~> A' ]0 )0)
          (f : V(0 V |- funF.-F[0 B ~> A ]0 )0),
          dat.-β|1 (Des ([1 f ~> funF.-F[0 B ~> A' ]0 ]0 <o funF.-F[1 1 ~> A' ]0 <o a)) ~~
                   Des ([1 dat.-β|1 f ~> funG.-F[0 B ~> A' ]0 ]0 <o funG.-F[1 1 ~> A' ]0 <o a).
    Proof.
      (** LHS **)
      intros; eapply TransV; [| eapply SymV, Cons_Output ].
      eapply TransV; [| eapply CongCom; [eapply ReflV| eapply Cons_Des] ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongConsIn, CongMetaF, Cat1LeftV ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongConsIn, metaF_arrow ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply ConsIn_Input ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongCom; [eapply ReflV|]; eapply Cat2V ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, SymV, Cat2V ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply Des_Input ].
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDes, SymV, ConsIn_consV10_functorial ].        
      eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply SymV, Des_Input ].
      eapply TransV; [| eapply  SymV, Des_Output ].
      eapply TransV; [| eapply  CongDes, SymV, Cat2V].
      eapply TransV; [| eapply  CongDes, CongCom; [|eapply ReflV] ; eapply SymV, ConsIn_Output2 ].
      eapply TransV; [| eapply  CongDes, CongCom; [|eapply ReflV] ; eapply CongConsIn, consV11_bifunctorial ].
      eapply TransV; [| eapply  CongDes, CongCom; [|eapply ReflV] ; eapply ConsIn_Input ].
      eapply TransV; [| eapply  CongDes, Cat2V ].
      eapply TransV; [| eapply  CongDes, CongCom; [eapply ReflV|] ; eapply SymV, Cat2V ].
      eapply TransV; [| eapply  CongDes, CongCom; [eapply ReflV|] ; eapply CongCom; [|eapply ReflV]; eapply metaβ_morphism   ].
      eapply TransV; [| eapply CongDes; eapply SymV, Cat2V]. 
      eapply TransV; [| eapply CongDes, CongCom; [| eapply ReflV]; eapply SymV, Cat2V].

      (** RHS **)
      eapply CongDes. eapply TransV; [ eapply Cat2V |]. eapply CongCom; [|eapply ReflV].
      eapply TransV; [ eapply CongCom; [eapply ReflV|];  eapply CongConsIn , CongMetaF, SymV, Cat1LeftV |].
      eapply TransV; [ eapply CongCom; [eapply ReflV|];  eapply CongConsIn , SymV, metaF_arrow |].
      eapply TransV; [ eapply CongCom; [eapply ReflV|];  eapply SymV, ConsIn_Input |].
      eapply TransV; [ eapply Cat2V |].
      eapply CongCom; [| eapply ReflV].

      (** more pure logic *)
      eapply TransV; [| eapply CongCom; [| eapply ReflV]; eapply CongConsIn, CongConsV10, CongDes, SymV, Cat1LeftV].
      eapply TransV; [| eapply SymV, ConsIn_Input].
      eapply TransV; [| eapply CongConsIn; eapply SymV, consV10_functorial].
      eapply TransV; [| eapply CongConsIn, CongConsV10,  SymV, Des_Cons ].
      eapply TransV; [| eapply CongConsIn, CongConsV10,  CongDes, Cat1LeftV ].
      eapply ConsIn_consV10_functorial.
    Qed.

    Lemma poly_of_metaβ_morphism_codomain:
      forall dat : data funF funG,
        class dat ->
        forall (V : obV log) (B : obA log) (W : obV log) 
          (B' : obA log) (b : V(0 W |- log .-A[0 B' ~> B ]0 )0) 
          (A : obA catA) (f : V(0 V |- funF.-F[0 B ~> A ]0 )0),
          dat.-β|1 (Des (log .-A[1 b ~> funF.-F|0 A ]0 <o f)) ~~
                   Des (log .-A[1 b ~> funG.-F|0 A ]0 <o dat.-β|1 f).
    Proof.
      (** LHS **)
      intros; eapply TransV; [| eapply SymV, Cons_Output ].
      eapply TransV; [| eapply CongCom; [eapply ReflV| eapply Cons_Des] ].

      (** RHS **)
      eapply TransV; [ eapply CongDes, CongCom; [eapply ReflV|];  eapply Cons_Output |].
      eapply TransV; [ eapply CongDes, CongCom; [eapply ReflV|];  eapply CongCom; [eapply ReflV|]; eapply SymV, Cons_Des |].
      eapply TransV; [ eapply CongDes, CongCom; [|eapply ReflV]; eapply ConsIn_DesIn |].
      eapply TransV; [ eapply CongDes, CongCom; [|eapply ReflV]; eapply CongConsIn, polyV_relV_polyV_relT |].
      eapply TransV; [ eapply CongDes, Cat2V |].
      eapply TransV; [ eapply CongDes, CongCom; [|eapply ReflV]; eapply ConsIn_Input |].
      eapply TransV; [ eapply CongDes, CongCom; [|eapply ReflV]; eapply CongConsIn, consV11_bifunctorial |].
      eapply TransV; [ eapply CongDes, CongCom; [|eapply ReflV]; eapply SymV, ConsIn_Input |].
      eapply TransV; [ eapply CongDes, SymV, Cat2V  |].
      eapply TransV; [ eapply CongDes, CongCom; [|eapply ReflV]; eapply CongConsIn, SymV, Cat1RightV |].
      eapply TransV; [ eapply CongDes, CongCom; [|eapply ReflV]; eapply SymV, ConsIn_Output2 |].
      eapply TransV; [ eapply CongDes, SymV, Cat2V  |].
      eapply TransV; [ eapply SymV, Des_Output  |].
      eapply TransV; [ eapply CongCom; [eapply ReflV |]; eapply CongDes, Cat2V |].
      eapply TransV; [ eapply CongCom; [eapply ReflV |]; eapply CongDes, CongCom; [|eapply ReflV]; eapply ConsIn_Input  |].
      eapply TransV; [ eapply CongCom; [eapply ReflV |]; eapply CongDes, CongCom; [|eapply ReflV]; eapply CongConsIn, Cat1LeftV  |].
      eapply TransV; [ eapply CongCom; [eapply ReflV |]; eapply CongDes, CongCom; [|eapply ReflV]; eapply CongConsIn, SymV, polyV_relV_polyV_relT  |].
      eapply TransV; [ eapply CongCom; [eapply ReflV |]; eapply CongDes, CongCom; [|eapply ReflV]; eapply SymV, ConsIn_DesIn  |].

      eapply ReflV.
    Qed.

    (** now class part**)
    Coercion classTransformation_of_classMetatransformation (dat : @data log catA funF funG) (ext : @class dat)
    : @TRANSFORMATION.class log catA (CATEGORY.category_of_logic log) funF funG dat :=
      @TRANSFORMATION.Class log catA (CATEGORY.category_of_logic log) funF funG
                            (dataTransformation_of_dataMetatransformation dat)
                            (poly_of_metaβ_arrow ext)
                            (poly_of_metaβ_morphism ext)
                            (poly_of_metaβ_morphism_codomain ext).
    
    Coercion transformation_of_metatransformation (trans : @metatransformation)
    : @TRANSFORMATION.transformation log catA (CATEGORY.category_of_logic log) funF funG
      := {| TRANSFORMATION.data_of :=  trans; TRANSFORMATION.class_of :=  trans |}.
    Canonical Structure transformation_of_metatransformation.
    
    (** theorem **)
    Import Ex_Notations.
    Definition typeof_metaβ_morphism :=  forall (trans : @metatransformation),  forall A A' : obA catA,
                                           [0 funF.-F|0 A ~> trans.-β||0 A' ]1 <o (funF) .-F||1 ~~
                                                                                 [1 trans.-β||0 A ~> funG.-F|0 A' ]0 <o (funG) .-F||1.
    Check  (fun trans: @metatransformation => @metaβ_morphism _ trans) : typeof_metaβ_morphism.
    Definition typeof_polyβ_morphism :=  forall (trans : metatransformation) (V : obV log) 
                                           (B : obA log) (A : obA catA) (W : obV log) 
                                           (A' : obA catA) (a : V(0 W |- catA .-A[0 A ~> A' ]0 )0)
                                           (f : V(0 V |- funF.-F[0 B ~> A ]0 )0),
                                           trans.-β|1 (Des([1 f ~> funF.-F[0 B ~> A' ]0 ]0 <o funF.-F[1 1 ~> A' ]0 <o a)) ~~
                                                      Des([1 trans.-β|1 f ~> funG.-F[0 B ~> A' ]0 ]0 <o funG.-F[1 1 ~> A' ]0 <o a).
    Check (fun trans: @metatransformation => @TRANSFORMATION.polyβ_morphism _ _ _ _  _ _ trans) : typeof_polyβ_morphism .

    Lemma metaβ_morphism_from_poly_of_metaβ : typeof_polyβ_morphism -> typeof_metaβ_morphism.
    Proof.
      (** LHS **)
      unfold typeof_metaβ_morphism, typeof_polyβ_morphism. intro H_poly_morphism. intros.
      specialize H_poly_morphism with (B := I) (A := A) (A' := A') (a := 1) (f := 1).
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply SymV, Cons_Output ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply Cons_Des ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongCom; [|eapply ReflV]; eapply SymV, consV10_functorial_fun1 ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, SymV, Cat1LeftV ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, SymV, Cat1RightV ]. 
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongConsIn, CongMetaF, Cat1LeftV ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongConsIn, metaF_arrow ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, ConsIn_Input ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply SymV, Des_Output ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongDes, SymV, Cat2V ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongDes, CongCom; [|eapply ReflV]; eapply SymV, ConsIn_Output2   ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongDes, SymV, ConsIn_Input   ].

      (** RHS **)
      eapply CongCons in H_poly_morphism.
      eapply SymV, TransV, SymV in H_poly_morphism; [|eapply Cons_Des]. eapply TransV in H_poly_morphism; [|eapply Cons_Des].
      eapply  TransV in H_poly_morphism; [|eapply CongCom; [eapply ReflV|]; eapply SymV, Cat1RightV ].
      eapply TransV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|];  eapply CongConsIn, CongMetaF, Cat1LeftV ].
      eapply TransV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|];  eapply CongConsIn, metaF_arrow].
      eapply TransV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|];  eapply ConsIn_Input].
      eapply TransV in H_poly_morphism; [| eapply SymV, Cat2V ].
      eapply TransV in H_poly_morphism; [| eapply CongCom; [|eapply ReflV]; eapply SymV, ConsIn_consV10_functorial ].
      eapply TransV in H_poly_morphism; [| eapply SymV, ConsIn_Input].
      eapply CongDesIn in H_poly_morphism.
      eapply SymV, TransV, SymV in H_poly_morphism; [|eapply DesIn_ConsIn]. eapply TransV in H_poly_morphism; [|eapply DesIn_ConsIn].        
      eapply TransV in H_poly_morphism; [| eapply CongCom; [|eapply ReflV];  eapply CongConsV10, CongDes, SymV, Cat1LeftV].
      eapply TransV in H_poly_morphism; [| eapply CongCom; [|eapply ReflV];  eapply CongConsV10, Des_Cons].
      eapply TransV in H_poly_morphism; [| eapply CongCom; [|eapply ReflV];  eapply consV10_functorial].
      eapply TransV in H_poly_morphism; [| eapply Cat2V].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [|eapply ReflV]; eapply consV11_bifunctorial ].
      eapply SymV, TransV, SymV in H_poly_morphism; [| eapply Cat2V ].
      eapply Des_I_Iso in H_poly_morphism.

      exact H_poly_morphism.
    Qed.

  End Context2.

  (**  __NEXT SECTION IS WHY : ALL THIS WORK OF INTERFACING FOR INSTANCES WAS DONE__
apply this to unfold this as identitary (external-structural) of composition (not really composition) of polyfunctors ( polyV_relV o (poly_of_meta F[0 B ~> - ]1) ) .. ( polyV_relV o (poly_of_meta metaFB) )  ...  show before that
1. some metafunctor metaFB into catV on top of F[0 B ~> - ]1  by polyF which becomes  metaFB := meta_of_poly F at B,
2.  then get derived polyfunctor from this metafunctor, 
3.  then unitary( |1 ) of this derived polyfunctor is  identitary( ||1 ) of the metafunctor metaFB on top of F[0 B ~> - ]1 
4.  which is  identitary ( [B ~> - ]1 ) of original polyfunctor F  all:
( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 A' X   (polyF is functor)
( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o (meta_of_ polyF at B)||1 A' X  ( meta_IdenV  ||1 , definitionally )
(    ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o FB||1 A' X    )
( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o (poly_of_ (meta_of_ polyF at B))|1 A' X (poly_of_meta is functorToCat  ,  propositionally)
(poly_of_meta metaFB)[0 V ~> - ]1 A' X   ALT   (polyV_relV_funToCat o (poly_of_meta metaFB))[0 V ~> - ]1 A' X (propositionally funComp_idenV_rel_F'_IdenV_F_unitB... ?may relate functorToCat_unitB  |1 with functor_IdenV  [0 B ~> - ]1 ? )
(meta_of_poly (poly_of_meta (meta_of_poly F at B)) at V)||1 A' X   ALT  (meta_of_poly (polyV_relV_funToCat o (poly_of_meta (meta_of_poly F at B))) at V)||1 A' X
.... V( A[A' ~> X] |- [ V[V ~> F[B ~> A']] ~> V[V ~> F[B ~> X]] ] )  .... as above

  Definition natural (V : obV) (B : obB) (A : obA) (β : forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0) :=
                        forall (C X : obA),
                          ( [0 A[0 A ~> C ]0 ~> β X ]1
                            <o A[0 A ~> - ]1 C X )
                            ~~ ( [1 β C ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
                                 <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) .

  Definition natural (V : obV) (B : obB) (A : obA) 
                        (β : forall X : obA, V(0 (meta_of_poly polyA at A)|0 X  |- (meta_of_poly (polyV_relV o (poly_of_meta (meta_of_poly F at B))) at V)|0 X )0) :=
                        forall (A' X : obA),
                          ( [0 (meta_of_poly polyA at A)|0 A' ~> β X ]1
                            <o (meta_of_poly polyA at A)||1 A' X )
                            ~~ ( [1 β A' ~> (meta_of_poly (polyV_relV o (poly_of_meta (meta_of_poly F at B))) at V)|0 X ]0
                                 <o (meta_of_poly (polyV_relV o (poly_of_meta (meta_of_poly F at B))) at V)||1 A' X ) .
      ... == natural_metatransformation from (meta_of_poly polyA at A) to (meta_of_poly (polyV_relV o (poly_of_meta (meta_of_poly F at B))) at V) by β at A' at X    **)
  Import METATRANSFORMATION.Ex_Notations. (*BUG , not working as expected*)
  Section Context3.
    Context {log : logic} {catA : category log} {catB : category log}.
    Variable (funF : functorToCat (form_of_functor catA) catB).
    Variables (V : obV log) (B : obB funF) (A : obB catA).
    Variable ( imageβ : forall X : obA catA, V(0 ((@metafunctor_of_functor_at _ catA A).-F|0 X)%meta |-
                                          ((@metafunctor_of_functor_at _ (@functorToCat_of_metafunctor _ _ (@metafunctor_of_functor_at _ funF B)) V).-F|0 X)%meta )0 ).
    Let imageβ_as_data := @Data log (@form_of_functor _ catA) (@metafunctor_of_functor_at _ catA A) (@metafunctor_of_functor_at _ (@functorToCat_of_metafunctor _ _ (@metafunctor_of_functor_at _ funF B)) V) imageβ
                          : @data log (@form_of catA) (meta_of catA A) (meta_of (meta_of funF B) V).
    
    Check eq_refl : ( @natural = ( fun (log : logic) (dat_ : FUNCTOR.data) (func : FUNCTOR.class dat_)
                                     (V : obV log) (B : obB func) (A : obA func)
                                     (β : forall X : obA func, V(0 func.-A[0 A ~> X ]0 |- [0 V ~> func.-F[0 B ~> X ]0 ]0 )0) => forall Y X : obA func,
                                                                                                                           ( [0 func.-A[0 A ~> Y ]0 ~> β X ]1 <o (func.-A[0 A ~> - ]1) Y X
                                                                                                                             : V(0 func.-A[0 Y ~> X ]0  |- [0 func.-A[0 A ~> Y ]0 ~> [0 V ~> func.-F[0 B ~> X ]0 ]0 ]0 )0 )
                                                                                                                             ~~ [1 β Y ~> [0 V ~> func.-F[0 B ~> X ]0 ]0 ]0 <o V[0 V ~> - ]1 _ _ <o (func.-F[0 B ~> - ]1) Y X ) ).
    Eval unfold natural in @natural log funF funF V B A imageβ.

    Definition typeof_metaβ_morphism_of_imageβ := forall A0 A' : @obA log (form_of catA),
                                                    [0 (meta_of catA A).-F|0 A0 ~> imageβ_as_data.-β||0 A' ]1 <o
                                                                                                                (meta_of catA A) .-F||1 ~~
                                                                                                                [1 imageβ_as_data.-β||0 A0 ~> (meta_of (meta_of funF B) V).-F|0 A' ]0 <o
                                                                                                                                                                                        (meta_of (meta_of funF B) V) .-F||1 .
    Check (@metaβ_morphism log (@form_of catA) (meta_of catA A) (meta_of (meta_of funF B) V) imageβ_as_data _) : typeof_metaβ_morphism_of_imageβ .

    Lemma soundness_natural_is_meta_polymorphism :  @natural log funF funF V B A imageβ -> typeof_metaβ_morphism_of_imageβ .
      unfold natural. unfold typeof_metaβ_morphism_of_imageβ.
      intros H_natural Y X. 
      do 2 rewrite meta_of_polyF_at_identitary_rel_polyF_identitary.
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply polyF_identitary_rel_polyF_unitB_metaFunc |]. 
      (*FASTER eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply (@polyF_identitary_rel_polyF_unitB_metaFunc log _ _ (meta_of funF B) V Y X) |]. *)
      eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [eapply ReflV|]; eapply SymV, poly_of_metaF_unitV_metaF_IdenV  |].
      rewrite meta_of_polyF_at_identitary_rel_polyF_identitary.
      eapply H_natural.
    Qed.

    Lemma soundness_meta_polymorphism_is_natural :  typeof_metaβ_morphism_of_imageβ -> @natural log funF funF V B A imageβ .
      unfold natural. unfold typeof_metaβ_morphism_of_imageβ.
      intros H_poly_morphism Y X. 
      specialize H_poly_morphism with  (A0 := Y) (A' := X).
      do 2 rewrite meta_of_polyF_at_identitary_rel_polyF_identitary in H_poly_morphism.
      eapply TransV in H_poly_morphism; [|eapply CongCom; [eapply ReflV|]; eapply SymV, polyF_identitary_rel_polyF_unitB_metaFunc ].
      eapply TransV in H_poly_morphism; [|eapply CongCom; [eapply ReflV|]; eapply CongCom; [eapply ReflV|]; eapply poly_of_metaF_unitV_metaF_IdenV].
      rewrite meta_of_polyF_at_identitary_rel_polyF_identitary in H_poly_morphism.
      eapply H_poly_morphism.
    Qed.
  End  Context3.

End METATRANSFORMATION.


(** ____ ADDENDUM ; TODO: TO BE RESOLVED LATER ____ **)
Module FUNCOMP.
  Import FUNCTOR.
  Import FUNCTORTOCAT.
  Import FUNCTOR.Ex_Notations4.
  Set Implicit Arguments.
  Unset Strict Implicit.

  (** possible but yoneda does not require polymorphism in B ,
  also memo that if B is category then presence of polyB_inputUnitB  *)
  Hypothesis polyF_morphism_codomain : forall (log : logic) (dat : @data log) (V : obV log) (B : obB dat),
                                       forall (A : obA dat) (W : obV log) (B' : obB dat) (b : V(0 W |- B[0 B' ~> B]0 )0),
                                       forall (f : V(0 V |-F[0 B ~> A ]0 )0) (X : obA dat),
                                         (* use ( B[1 g ~> F|0 A ]0 <o f  ) because no polyB_arrow is assumed *)
                                         F[1 Des( B[1 b ~> F|0 A ]0 <o f ) ~> X]0
                                          ~~ ( DesIn( [0 V ~> B[1 b ~> F|0 X ]0 ]1 <o F[1 f ~> X ]0 )
                                               : V(0 A[0 A ~> X ]0 |- [0 (0 V & W )0 ~> F[0 B' ~> X ]0 ]0 )0 ) .

  (** this lemma uses the hypothesis polyF_morphism_codomain polymorphism in B together with that B is category.
     alternative is to assume this lemma as axiom **)
  Lemma polyF_identitary_rel_polyF_unitB_ABORT:
    forall (log : logic) (catA : form log) (catB : category log)
      (funF : functorToCat catA catB) (B : obB catB) (A X : obA catA),
      (catB.-F[0 B ~> - ]1) funF.-F|0 A funF.-F|0 X <o F|1 A X ~~ (funF.-F[0 B ~> - ]1) A X .
  Proof.
    intros. eapply SymV. unfold polyF_unitB.
    eapply TransV; [eapply DesIdenObR_output|].
    generalize (@polyF_morphism_codomain  log funF _ (funF.-F|0 A) _ _ B 1 ((catB).-uA) X ); intros H_polyF_morphism_codomain.

    eapply SymV, TransV, SymV in H_polyF_morphism_codomain;
      [|eapply FUNCTORTOCAT.CongPolyF, CongDes; eapply ConsIdenObL_DesIdenObL ].
    eapply SymV, TransV, SymV in H_polyF_morphism_codomain;
      [|eapply FUNCTORTOCAT.CongPolyF, CongDes, CongConsIdenObL; eapply SymV, (@polyF_inputUnitA _ _ catB)  ].
    eapply SymV, TransV, SymV in H_polyF_morphism_codomain;
      [|eapply FUNCTORTOCAT.CongPolyF, Cat1LeftV].
    eapply SymV, TransV, SymV in H_polyF_morphism_codomain;
      [|eapply FUNCTORTOCAT.polyF_arrow].

    eapply CongConsIn in H_polyF_morphism_codomain.
    eapply TransV in H_polyF_morphism_codomain; [|eapply ConsIn_DesIn].

    eapply TransV; [eapply CongDesIdenObR, H_polyF_morphism_codomain |].
    eapply TransV; [eapply CongDesIdenObR, SymV, ConsIn_Input |].
    eapply TransV; [eapply SymV, DesIdenObR_Input |].
    eapply TransV; [| eapply Cat1LeftV ].
    eapply CongCom; [| eapply ReflV].
    eapply DesIdenObRConsIdenObL.
  Qed.
  
  Section Context.
    Context {log : logic} (catA : form log) (catB : category log) (catC : category log).
    Definition data := prod (FUNCTORTOCAT.data catA catB) (FUNCTORTOCAT.data (form_of_functor catB) catC).
    Variable data_funF_data_funF' : data.

    Definition composition_F'_after_F :
      forall (V : obV log) (B : obA catB) (A : obA catA),
      forall (b : V(0 V |- catB.-A[0 B ~> (data_funF_data_funF'.(fst)).-F|0 A ]0 )0),
      forall (W : obV log) (C : obA catC),
      forall (c : V(0 W |- catC.-A[0 C ~> (data_funF_data_funF'.(snd)).-F|0 B]0 )0),
      forall X : obA catA, V(0 A[0 A ~> X ]0  |- [0 V ~> [0 W ~> catC.-A[0 C ~> (data_funF_data_funF'.(snd)).-F|0 (data_funF_data_funF'.(fst)).-F|0 X ]0 ]0 ]0 )0.
    Proof.
      intros.
      eapply @polyV_relT_identitary (* _ <o _ *). apply consV01.
      eapply (@FUNCTOR.polyF log (data_funF_data_funF'.(snd)) _ _ _ c).
      eapply (@FUNCTOR.polyF log (data_funF_data_funF'.(fst)) _ _ _ b).
    Defined.

    Definition composition_F'_after_F_simple :
      forall  (A : obA catA),
      forall (W : obV log) (C : obA catC),
      forall (c : V(0 W |- catC.-A[0 C ~> (data_funF_data_funF'.(snd)).-F|0 (data_funF_data_funF'.(fst)).-F|0 A ]0 )0),
      forall X : obA catA, V(0 A[0 A ~> X ]0  |- [0 W ~> catC.-A[0 C ~> (data_funF_data_funF'.(snd)).-F|0 (data_funF_data_funF'.(fst)).-F|0 X ]0 ]0 )0.
    Proof.
      intros.
      apply DesIdenObR.
      eapply composition_F'_after_F.
      eapply (@unitA _ catB).
      exact c.
    Defined.

    Definition dataFunToCat_of_dataFunComp : FUNCTORTOCAT.data catA catC :=
      {|
        FUNCTORTOCAT.polyF0 := fun A  => (data_funF_data_funF'.(snd)).-F|0 (data_funF_data_funF'.(fst)).-F|0 A;
        FUNCTORTOCAT.polyF := fun V C A c X =>  composition_F'_after_F_simple c X |}.
  (* econstructor.
     Unshelve. 2: intro A; exact ((data_funF_data_funF'.(snd)).-F|0 (data_funF_data_funF'.(fst)).-F|0 A).
     intros; eapply composition_F'_after_F_simple. assumption.
   *)
  End Context.
  Coercion dataFunToCat_of_dataFunComp : data >-> FUNCTORTOCAT.data.

  Section Context2.    
    Context {log : logic} {catA : form log} {catB : category log} {catC : category log}.

    Definition class (data_funF_data_funF' : data catA catB catC ) := prod (FUNCTORTOCAT.class  (data_funF_data_funF'.(fst))) (FUNCTORTOCAT.class (data_funF_data_funF'.(snd))).
    Existing Class class.
    
    Variable  (data_funF_data_funF' : data catA catB catC ).
    Variable (class_funF_class_funF' : class data_funF_data_funF').

    Definition classFunToCat_of_classFunComp : @FUNCTORTOCAT.class _ _ _ (dataFunToCat_of_dataFunComp data_funF_data_funF') .
      destruct data_funF_data_funF' as [data_funF data_funF'].
      destruct  class_funF_class_funF' as [class_funF   class_funF' ].
      econstructor. 
      + cbn.  intros.  simpl dataFunToCat_of_dataFunComp.  simpl. 
        unfold composition_F'_after_F_simple , composition_F'_after_F .
        cbn.  cbn -[dataFun_of_dataFuntoCat].
        simpl dataFunToCat_of_dataFunComp.
        
        eapply TransV; [ eapply DesIdenObR_output|]. eapply CongDesIdenObR.
        eapply TransV; [ eapply Cat2V |]. eapply CongCom; [| eapply ReflV ].
        eapply TransV; [ eapply consV01_functorial  |].
        eapply CongConsV01.
        eapply FUNCTORTOCAT.polyF_arrow.

      + (**   (f _v o>F'F g _w) o>F'F h :=
  (f _v o>F' (1 o>F g _w)) o>F' (1 o>F h)  ~~  (by polyF'_morphism)
  f _v o>F' ( ( 1 o>F g _w)  o>B (1 o>F h) )  ~~  by Hypothesis polyF_identitary_rel_polyF_unitB_ABORT
  f _v o>F' ( (( 1 o>F g _w)  o>B 1) o>F h )  ~~  by polyB_inputUnitB from that B is category
  f _v o>F' (  ( 1 o>F g _w) o>F h )  ~~  (by polyF_morphism)
 f _v o>F' (1 o>F (g _w o>A h )) =:
 f _v o>F'F (g _w o> h )    **)
        
        intros. cbn. simpl.
        unfold composition_F'_after_F_simple , composition_F'_after_F . cbn.
        eapply TransV; [|  eapply DesIdenObR_output ].
        eapply TransV; [| eapply CongCom; [|eapply ReflV]; eapply FUNCTORTOCAT.CongPolyF, CongDes; eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply DesIdenObR_output ].
        eapply TransV; [| eapply CongCom; [|eapply ReflV]; eapply FUNCTORTOCAT.CongPolyF, CongDes; eapply CongCom; [eapply ReflV|]; eapply Cat2V ].
        eapply TransV; [| eapply CongCom; [|eapply ReflV]; eapply FUNCTORTOCAT.polyF_morphism ].
        eapply TransV; [| eapply DesIn_Input ].
        eapply CongDesIn.

        (* RHS *)
        eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongConsV01, SymV, DesIdenObR_output  |].
        eapply TransV; [| eapply Cat2V].
        eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV];  eapply (@CongPolyA log catB catB), Cat1LeftV ].
        eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply (@polyF_arrow log catB catB) ].
        eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply Cat2V ].
        eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongCom; [eapply ReflV|]; eapply (@polyF_identitary_rel_polyF_unitB_ABORT log catA catB (FunctorToCat class_funF) _ _ X  )]. cbn.
        eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply SymV, (@polyF_arrow log data_funF class_funF ) ].
        eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply (@CongPolyF log data_funF class_funF), SymV, Cat1LeftV ].
        eapply TransV; [ eapply CongCom; [| eapply ReflV]; eapply SymV, consV01_functorial |].
        eapply TransV; [ eapply SymV, Cat2V |].
        eapply CongCom; [eapply ReflV|].

        (*final clean LHS*)
        eapply TransV; [| eapply FUNCTORTOCAT.CongPolyF, SymV, DesIdenObR_Input  ].
        eapply TransV; [| eapply FUNCTORTOCAT.CongPolyF, CongDesIdenObR, CongCom; [|eapply ReflV]; eapply FUNCTORTOCAT.CongPolyF,  Cat1LeftV  ].
        eapply TransV; [| eapply FUNCTORTOCAT.CongPolyF, CongDesIdenObR, CongCom; [|eapply ReflV]; eapply FUNCTORTOCAT.polyF_arrow   ].
        eapply TransV; [| eapply FUNCTORTOCAT.CongPolyF, CongDesIdenObR, Cat2V ].
        eapply TransV; [| eapply FUNCTORTOCAT.CongPolyF, CongDesIdenObR, SymV, Cons_Des  ].
        eapply TransV; [| eapply FUNCTORTOCAT.CongPolyF, CongDesIdenObR, CongCons, Cat1RightV  ].
        eapply TransV; [| eapply FUNCTORTOCAT.CongPolyF, CongDesIdenObR, SymV, Cons_Output ].
        eapply TransV; [| eapply FUNCTORTOCAT.CongPolyF, DesIdenObR_output ].
        eapply TransV; [| eapply FUNCTORTOCAT.polyF_arrow ].

        (*final clean RHS*)
        eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongConsV01, CongDesIdenObR, SymV, Cat1LeftV  |].
        eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongConsV01, SymV, DesIdenObR_Input  |].
        eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply SymV, consV01_functorial  |].
        eapply TransV; [eapply SymV, Cat2V  |].
        eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply ConsIn_DesIn  |].
        eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongConsIn, SymV, Cat1LeftV  |].
        eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply SymV, ConsIn_Input  |].
        eapply TransV; [eapply Cat2V  |].

        eapply TransV; [|eapply CongCom; [eapply ReflV|]; eapply FUNCTORTOCAT.polyF_morphism ].
        eapply CongCom; [|eapply ReflV].

        eapply DesIdenObRInCons.
        
      +  intros. cbn. simpl.
         unfold composition_F'_after_F_simple , composition_F'_after_F . cbn.
         eapply CongDesIdenObR. eapply CongCom; [|eapply ReflV]. eapply CongConsV01.
         eapply FUNCTORTOCAT.CongPolyF . assumption.

      +   (**  f o>F'F unitA  := f o>F' (unitB o>F unitA)  ~~ (f o>F' (unitB) ) ~~ f  **)
        intros. cbn. simpl.
        unfold composition_F'_after_F_simple , composition_F'_after_F . cbn.
        eapply TransV; [eapply CongDesIdenObL, CongCom; [|eapply ReflV]; eapply SymV, DesIdenObR_output  |].
        eapply TransV; [eapply CongDesIdenObL, SymV, Cat2V  |].
        eapply TransV; [eapply CongDesIdenObL, CongCom; [eapply ReflV|]; eapply DesIdenObR_Input  |].
        eapply TransV; [eapply CongDesIdenObL, CongCom; [eapply ReflV|]; eapply CongDesIdenObR |].
        eapply TransV; [eapply SymV, ConsIdenObL_DesIdenObL|].
        eapply CongConsIdenObL, (@FUNCTORTOCAT.polyF_inputUnitA _ _ _ _ class_funF).
        eapply TransV; [eapply CongDesIdenObL, CongCom; [eapply ReflV|]; eapply DesIdenObR_ConsIdenObL|] .
        eapply (@FUNCTORTOCAT.polyF_inputUnitA _ _ _ _ class_funF').
    Qed.

  End Context2.
  Coercion classFunToCat_of_classFunComp : class >-> FUNCTORTOCAT.class.
  
  Section Context3.
    Context {log : logic} {catA : form log} {catB : category log} {catC : category log}.

    Structure funComp :=
      FunComp {
          data_of :> data catA catB catC;
          class_of :> class data_of; }.

    Global Existing Instance class_of.
    
    Coercion funtorToCat_of_funComp (funC : funComp) : functorToCat catA catC :=
      {| FUNCTORTOCAT.data_of := dataFunToCat_of_dataFunComp funC;
         FUNCTORTOCAT.class_of := classFunToCat_of_classFunComp funC |}.

    Variable (funF : FUNCTORTOCAT.functorToCat catA catB).
    Variable (funF' : FUNCTORTOCAT.functorToCat (form_of_functor catB) catC ).

    Definition funComp_of_seq_functorToCat : funComp :=
      {| data_of := (FUNCTORTOCAT.data_of funF, FUNCTORTOCAT.data_of funF');
         class_of := (FUNCTORTOCAT.class_of funF, FUNCTORTOCAT.class_of funF') |}.
  End Context3.
  
  Notation funCom funF funF' := (funtorToCat_of_funComp (funComp_of_seq_functorToCat funF funF')).

  Import FUNCTORTOCAT.Ex_Notations6.
  Section Context4.
    Context {log : logic} {catA : form log} {catB : category log} {catC : category log}.
    Variable (funF : FUNCTORTOCAT.functorToCat catA catB).
    Variable (funF' : FUNCTORTOCAT.functorToCat (form_of_functor catB) catC ).

    (** memo that may be simply the particular where funF' is catB **)
    Lemma composition_F'_after_F_identitary_polyF'_identitary_polyF_unitary :    forall (C : obA catC) (A X : obA catA),
                                                                                   (funF'.-F[0 C ~> - ]1) funF.-F|0 A funF.-F|0 X <o funF.-F|1 A X ~~ ((funCom funF funF').-F[0 C ~> - ]1) A X.
    Proof.
      intros. apply SymV, DesIdenObR_output.
    Qed.
  End Context4.
End FUNCOMP.
