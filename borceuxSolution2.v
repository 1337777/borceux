(*+ borceuxSolution.v +*)

(******************************************

Proph

https://github.com/1337777/borceux/blob/master/borceuxSolution.v

1. Short: This [1] solves some question of Ahrens [2] and Kan-Riehl [3], which is how to program Kelly's <<enriched categories>> and how the inter-dependence of <<naturality>> with <<category>> is cyclic. Also This [4] attempts to clarify the contrast <<categorical algebra>> (ring/locale-presentation and its "internal logic"), from <<categorial logic>> in the style of the <<enriched/encoded/programmed/recursion>> categories of Kelly-Dosen or Lawvere-Lambek and as attempted in [5], for example : the yoneda lemma and most categorial lemmas are no-more-than Gentzen's constructive logic of re-arranging the input-output positions <<modulo naturality>>. Now homotopy/knots/proof-nets may be held as (faithfull or almost-faithfull) semantical techniques (<<descent>>) to do this <<categorial logic>>, and the homotopy itself may be programmed in specialized grammars (for example [6] or HOTT).

2. The common assumption that catC( - , X ) is dual to catC( Y , - ) is FALSIFIED. This falsification originates from the description of the composition as some binary form instead of as some functional form which is programmed/encoded/enriched onto the computer. Then get some new thing which is named <<polymorphism>> from which to define <<polymorph category>>. This is the only-ever real description and deduction of the yoneda lemma, which says that the image of polyF (which is injective and contained in natural transformations) also contains all natural transformations.

3. Some polymorph category is given by polyF, which is commonly ( _1 o> _2 ), polymorph in V and polymorph in A :
 Variable obF : Type.
 Variable polyF00 : obF -> obF -> obV.
 Notation "F[0 B ~> A ]0" := (polyF00 B A) (at level 25).
 Parameter polyF : forall (B : obF), forall (V : obV) (A : obF),
                     V(0 V |- F[0 B ~> A ]0 )0 ->
                     forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0.

4. And to get polymorph functor, instead of describing F : catA --> catB  then (contrast yoneda structures) describe catV[ V , catB[ B , F - ] ] : catA --> catV , more precisely
  Variable polyF0 : obA -> obB.
  Notation "F|0 A" := (polyF0 A) (at level 4, right associativity).
  Notation "F[0 B ~> A ]0" := (B[0 B ~> F|0 A ]0) (at level 25).
  Parameter polyF : forall (V : obV) (B : obB) (A : obA),
                      V(0 V |- F[0 B ~> A ]0 )0 ->
                      forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0.

5. And to get polymorph transformation, instead of describing phi A : G A -> H A  then a-la-dosen (contrast weighted colimiting Kan extension) describe phi _f : catV( V , catB[ B , G A ] ) ->  catV( V , catB[ B , H A ] ) , more precisely
   Parameter poly_phi : forall (V : obV) (B : obB) (A : obA),
                       V(0 V |- F[0 B ~> A ]0 )0 ->
                       V(0 V |- G[0 B ~> A ]0 )0 .
And finally one shall relate the earlier <<naturality of transformation inside catV>> to this new <<polymorphism>> of transformation.

6. The earlier texts refering to Maclane associativity coherence and Dosen semiassociativity coherence and Dosen cut elimination for adjunctions and Chlipala ur/web database programming are all related to this present text which is how to program logically-enriched categories.

7. Stake for nondependent Solution Programme Seminary at FMCS2016 and ICMS2016 :
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
Set Universe Polymorphism.
(** ** NEXT1: use (+) record structure packaking interface with (+) semi-automatic semi-programmed canonical resolution/synthesis of the polymorphicity extras which is (+) on top of the data of objects and composition. Also note that any instance of the logic interface V shall be passed as parameter to the functor interface
 **)

(** **NEXT2: is it necessary, for efficient semi-automatic semi-programmed canonical resolution/synthesis of the polymorphicity extras,  that one shall express polymorphicity as naturality in the ultimate Coq meta logic T ? Or is polymorphicity-as-is workable ? **)

(** ** ultimate meta logic (Coq type theory) T , which enrich all the subject logics instances of the interface V **)

(** T on top of Type is instance of meta/logical category with interface V , 
+    any instance of interface V is enriched in T , 
+    T is both ordinary (in T) and enriched in itself T where ordinary (0 _ |- _ )0 coincide with enriched [0 _  ~> _ ]0  ,
+    polymorphicity (polyF_morphism or polyF_arrow) of category or functor  is naturality (metaα_morphism or metaυ_morphism) of meta transformation polyF (in index A or index V) where meta is the T instance of interface V

later, top interface is  polyfunctor (which is family of metafunctors with shared category-family ), get category by putting F is identity : obA -> obB := obA   and now polyF_morphism becomes the wanted polyA_morphism ,   get metafunctor by putting F is constant : obA -> obB := unit   and now polyF_morphism becomes the wanted metaF_morphism

later rename polyF_unitary to polyF_constant because some constant family is same as pointing at result (or shrinking the inputdomain)   ,         keep polyF_identitary
 **)

(** TODO : in polyF_morphism, change DesIn( [0 W ~> F[1 f ~> X ]0 ]1 <o F[1 g ~> X ]0 ) to DesIn( [0 W ~> F[1 f ~> X ]0 ]1 ) <o F[1 g ~> X ]0 
 **)

Definition obT : Type := Type. 
Definition polyT_relT00 : obT -> obT -> obT := fun T1 T2 => T1 -> T2.
Notation "T(0 B |- A )0" := (polyT_relT00 B A) (at level 35).

(** comprehended as conversion on the enriched data **)
(*Inductive convT : forall T1 T2, T(0 T1 |- T2)0 -> T(0 T1 |- T2 )0 -> Prop :=
  convT_Base : forall T1 T2 f g,  (forall t1, f t1 = g t1) -> @convT T1 T2 f g
| convT_Step : forall T1 T21 T22 f g,  (forall t1 ,  (@convT T21 T22 (f t1) (g t1))) -> @convT T1 (T21 -> T22) f g.
*)
Definition convT : forall T1 T2, T(0 T1 |- T2)0 -> T(0 T1 |- T2 )0 -> Prop := fun T1 T2 => eq . (*forall t1, f t1 = g t1.*)
Notation "v2 ~~T v1" := (convT v2 v1)  (at level 70).
Lemma ReflT : forall A1 A2 (f : T(0 A1 |- A2 )0), f ~~T f.
Proof.
(*  intros. apply convT_Base. reflexivity.*)
  (*  intros; intro; intros. reflexivity.*)
  reflexivity.
Qed.

Lemma SymT : forall A1 A2,  forall (f' f : T(0 A1 |- A2)0), f ~~T f' -> f' ~~T f.
Proof.
(*  induction 1.
  constructor 1. intros. rewrite H. reflexivity.
  constructor 2.  assumption. *)
(* intros; intro; symmetry. apply H.*)
  (*  symmetry. assumption. *)
  symmetry. assumption.
Qed.

Lemma TransT : forall A1 A2, forall (uTrans f : T(0 A1 |- A2)0), uTrans ~~T f -> forall (f' : T(0 A1 |- A2)0), f' ~~T uTrans -> f' ~~T f.
Proof.
(*  intros ? ? ? ? H ? H0. intro. eapply eq_trans. apply H0. apply H. *)
  (*intros; eapply eq_trans; eassumption.*)
  intros; eapply eq_trans; eassumption.
Qed.

Definition polyT_relT : forall (T : Type), forall (B : obT), forall (A : obT),
                          ( T -> T(0 B |- A )0 ) ->
                          forall X : obT, T(0 A |- X )0  ->  ( T -> T(0 B |- X )0 )
  := (fun (T : Type) (B : obT)  (A : obT) (f : T -> T(0 B |- A )0) 
        (X : obT) (g : T(0 A |- X )0) (t : T) (b : B) =>   g (f t b)) .

(** almost same as the common unitary .. but no unit-picking mentionned **)
Definition polyT_relT_unitary : forall (B : obT), forall (A : obT),
                                  T(0 B |- A )0 -> forall X : obT, T(0 A |- X )0  -> T(0 B |- X )0
  := (fun (B A : obT) (f : T(0 B |- A )0) (X : obT) (g : T(0 A |- X )0) =>
        polyT_relT (fun _ : unit => f) g tt) .  

Definition polyT_relT_identitary : forall (B : obT), forall (A : obT),
                                   forall X : obT, T(0 A |- X )0  -> T(0 B |- A )0 -> T(0 B |- X )0
  :=  fun (B : obT) => fun (A : obT) =>
                      fun X : obT =>  fun (a : T(0 A |- X )0) => fun (b : T(0 B |- A )0) =>
                                                            @polyT_relT (T(0 B |- A )0) B A (fun b0 => b0) X a b .

Notation "T(1 b |- X )0" := (@polyT_relT _ _ _ b X) (at level 35).

Notation "T(1I b |- - )0" := (@polyT_relT_unitary _ _ b) (at level 35).
(**  more precisely ( ( b 0 ) o> _ )   **)
Notation "T(1I b |- X )0" := (@polyT_relT_unitary _ _ b X) (at level 35).
(**  more precisely ( ( b 0 ) o> a )  **)
Notation "b o>> a" := (@polyT_relT_unitary _ _ b _ a) (at level 33, right associativity).
Eval compute in  fun b a => b o>> a .

Notation "T(1 'id' |- X )0" := (@polyT_relT_identitary _ _ X) (at level 35).
Notation "T(0 X |- - )1" := (@polyT_relT_identitary _ _ X) (at level 35).
(**  more precisely ( ( id _ ) o> a )  **)
Notation "T(0 X |- a )1" := (@polyT_relT_identitary _ _ X a) (at level 35).
(**  more precisely ( ( id b ) o> a )  **)
Notation "a <<o b" := (@polyT_relT_identitary _ _ _ a b) (at level 33, right associativity).
Eval compute in  fun b a => a <<o b .

Lemma polyT_relT_arrow :  forall (B : obT), forall (A : obT),
                          forall (T T' : Type) (b : T' -> T),
                          forall (f : T -> T(0 B |- A )0 ) (X : obT),
                          forall (a : T(0 A |- X )0), forall (ttt: T'),
                            T(1 (fun v' => f (b v')) |- X )0 a ttt
                             ~~T T(1 f |- X )0 a (b ttt) .
Proof.
  (*  intros; intro. reflexivity.*)
  reflexivity.
Qed.

Lemma polyT_relT_unitary_rel_identitary :  forall (B : obT) , forall (A : obT) ,
                                           forall X : obT , forall (a : T(0 A |- X )0),  forall (b : T(0 B |- A )0),
                                             @polyT_relT_unitary B A b X a ~~T  a <<o b  . (* @polyT_relT B (T(0 B |- A )0) A (fun b0 => b0) X a b .*)
Proof. (* instance-proof copy-paste*)
(*  unfold polyT_relT_identitary. unfold polyT_relT_unitary.
  intros; intro; eapply polyT_relT_arrow with (f := fun b0 => b0) (b := fun _ : unit => b).*)
  reflexivity.
Qed.


(*
Definition convT_fun : forall U1 U2 T1 T2, (T(0 U1 |- U2)0 -> T(0 T1 |- T2)0) -> (T(0 U1 |- U2)0 -> T(0 T1 |- T2 )0) -> Prop
  := fun  U1 U2 T1 T2 (w' w : (T(0 U1 |- U2)0 -> T(0 T1 |- T2)0)) =>
       forall u1 u2, u1 ~~T u2 -> w' u1 ~~T w u2 .
Notation "w' ~~~T w" := (convT_fun w' w)  (at level 70).
*)
Lemma Cong_polyT_relT :   forall (V : obT) (B A : obT) (f f' : T(0 V |- T(0 B |- A )0 )0),
                            (forall _v : V, f' _v ~~T f _v) -> forall X : obT,  forall a1 a2, a1 ~~T a2 -> forall _v, T(1 f' |- X )0 a1 _v ~~T T(1 f |- X )0 a2 _v .
  intros. compute. rewrite H, H0. reflexivity.
Qed.

(*
Axiom Cong_polyT_relT :   forall (V : obT) (B A : obT) (f f' : T(0 V |- T(0 B |- A )0 )0),
                                f' ~~T f -> forall X : obT, T(1 f' |- X )0 ~~T T(1 f |- X )0.

Axiom Cong_polyT_relT' : forall (B : obT), forall (A : obT),
                  forall (f f' : T(0 B |- A )0),
                    f' ~~T f -> forall X : obT, @polyT_relT_unitary B A f' X ~~~T @polyT_relT_unitary B A f X. *)
(*Proof.
  (*  intros. intro. intros. unfold convT in * . f_equal; assumption. *) 
  intros. intro. intros. unfold convT in * . intros.  compute. (* solve [congruence]. *)
  rewrite H. apply H0.
Qed.*)

Definition idT : forall T : Type, T -> T := fun T : Type => fun x : T => x .
Definition IdenT : forall {T : obT}, T(0 T |- T )0 := idT .
Notation "1T" := (@IdenT _) (at level 0).

(** related to non-variance when unit pull the input, commonly  ( 1 o> h ) ~~ h  **)
Lemma polyT_relT_unitT : forall (A : obT), forall X : obT, forall a1 a2, a1 ~~T a2 -> ( @idT (T(0 A |- X )0)  ) a1 ~~T ( T(1I (@IdenT A) |- X )0 ) a2 .
Proof.
  intros.  intros. assumption.
Qed.

(** related to non-variance when unit push the output, commonly  ( (f _i) o> 1 ) ~~ (f _i)  , 
       therefore polyT is injective **)
Lemma polyT_relT_inputUnitT : forall (B : obT), forall (A : obT),
                              forall (b : T(0 B |- A )0),
                                 b  ~~T ( (T(1I b |- A )0)  (@IdenT A) ) .
Proof.
(*  intros; intro; reflexivity.*) reflexivity.
Qed.
(** TODO: write the  functional monoidal logic onto T **)

Definition desT00 : forall V2 : obT, forall V1 : obT, obT.
  intros ? ? . exact (prod V1 V2). Defined.
Definition desT10 : forall V2 : obT, forall V1 V1', (polyT_relT00 V1 V1') -> (polyT_relT00 (desT00 V2 V1) (desT00 V2 V1')).
  intros ? ? ? v (_v1, _v2). exact (v _v1, _v2). Defined.
Definition consT00 : obT -> obT -> obT.
  intros V1 V2. exact ( (V1 -> V2) % type). Defined.
Definition consT01 : forall V1 : obT, forall V2 V2', (polyT_relT00 V2 V2') -> (polyT_relT00 (consT00 V1 V2)  (consT00 V1 V2')).
  intros ? ? ? v2 v12.  exact (fun _v1 => v2 ( v12 _v1 ) ). Defined.
Definition consT10 : forall V1' V1, (polyT_relT00 V1' V1) -> forall V2 : obT, (polyT_relT00 (consT00 V1 V2) (consT00 V1' V2)).
  intros ? ? v1 ? v12 .  exact (fun _v1' => v12 (v1 _v1') ). Defined.
Definition DesT: forall V : obT, forall (U W : obT), (polyT_relT00 U (consT00 V W)) -> (polyT_relT00 (desT00 V U) W) .
  intros ? ? ? u'v'w. exact (fun _u_v => let (_u, _v) := _u_v in u'v'w _u _v ). Defined.
Definition ConsT : forall V : obT, forall (U W : obT), (polyT_relT00 (desT00 V U) W) -> (polyT_relT00 U (consT00 V W)).
  intros ? ? ? uv'w. exact (fun _u => fun _v => uv'w (_u, _v) ). Defined. 
Definition IdenObT : obT.
  exact unit. Defined.
Definition unitT : forall {A : obT}, (polyT_relT00 IdenObT (consT00 A A) ).
  intros ? ?. exact (fun a => a). Defined.
Definition AssocT : forall {V W :obT }, forall {U: obT }, T(0 (desT00 (desT00 W V )  U ) |- (desT00 W ( (desT00 V  U))  ) )0.
  intros. intro. destruct X. destruct d. exact ((u,v ),w).
Defined.


About consT01.
Notation  "(0T V1 * V2 )0" := (desT00 V2 V1) (at level 30, V1 at next level).
Notation  "(1T v * V2 )0" := (@desT10 V2 _ _ v) (at level 30, v at next level).
Notation "[0T V1 ~> V2 ]0" := (consT00 V1 V2) (at level 30).
Notation "[0T V1 ~> v ]1" := (@consT01 V1 _ _ v) (at level 30).
Notation "[1T v ~> V2 ]0" := (@consT10 _ _ v V2) (at level 30).
Notation  "'IT'" := (@IdenObT _) (at level 0).
Notation "'uT'" := (@unitT _) (at level 0).


Lemma CongDesT : forall V : obT, forall (U W : obT), forall (f f' : T(0 U |- [0T V ~> W ]0 )0),
                  f' ~~T f -> DesT f' ~~T DesT f .
(*  intros ? ? ? ? ? H t1.
  destruct t1. simpl. rewrite H. reflexivity.*)
    intros ? ? ? ? ? H .
   simpl. rewrite H. reflexivity.
Qed.
Axiom Des_ConsT : forall V : obT, forall (U W : obT), forall (f : T(0 (0T U * V )0 |-  W )0),
                    DesT (ConsT f) ~~T f .
(*Proof.
  (*  intros. intros [ ]. reflexivity.*)
Qed.*)

Axiom Des_OutputT : forall V : obT , forall (U W : obT ), forall (v : T(0 U |- T(0 V |- W )0 )0), forall W' (w : T(0 W |- W' )0),
                           DesT( [0T V ~> w ]1 <<o v ) ~~T w <<o DesT( v ) .
(*Proof.
  (*  intros. intros []. intros. reflexivity.*)
Qed.*)

(* this is some form of functional extensionality *)
Lemma CongConsT : forall V : obT, forall (U W : obT), forall (v v' : T(0 (0T U * V )0 |- W )0 ),
                    v' ~~T v -> ConsT v' ~~T ConsT v .
Proof.
  intros. compute. rewrite H. reflexivity.
Qed.
  Lemma Cons_DesT : forall V : obT, forall (U W : obT), forall (f : T(0 U |-  [0T V ~> W ]0 )0),
                    ConsT (DesT f) ~~T f .
    (*    intros. intro.  reflexivity. *)
        reflexivity.
Qed.

Lemma Cons_InputT : forall V : obT, forall (U U' : obT) (w : T(0 U' |- U )0), forall (W : obT) (v : T(0 (0T U * V )0 |- W )0),
                         ConsT(v <<o (1T w * V )0 )  ~~T ConsT( v ) <<o w .
  (*  intros. intro. reflexivity.*)
  intros.  reflexivity.
Qed.

Definition DesInT : forall (V : obT), forall (U0 U1 W : obT), T(0 U0 |- [0T U1 ~> [0T V ~> W ]0 ]0 )0 -> T(0 U0 |- [0T (0T U1 * V )0 ~> W ]0 )0.
  intros. apply ConsT. eapply polyT_relT_identitary. Check @AssocT. 2: eapply (@AssocT _ _ _).  eapply DesT.
  eapply DesT. exact X.
Defined.

Axiom  functional_extensionality_dep : forall {A} {B : A -> Type},
                                       forall (f g : forall x : A, B x),  (forall x, f x = g x) -> f = g.

Lemma  polyT_relT_morphism'' :   forall (V : obT) (B A : obT) (W : obT) (A' : obT)
                                   (g : T(0 W |- T(0 A |- A' )0 )0) (f : T(0 V |- T(0 B |- idT A )0 )0)
                                   (X : obT),
                                   T(1 DesT
                                       ((T(1 (fun b0  => b0) |- [0T V ~> T(0 B |- idT A' )0 ]0 )0)
                                          ([1T f ~> T(0 B |- idT A' )0 ]0)
                                          ((T(1 (fun b0  => b0) |- [0T T(0 B |- idT A )0 ~> T(0 B |- idT A' )0 ]0 )0)
                                             (T(1 ( IdenT ) |- A' )0) g)) |- X )0 ~~T
                                    DesInT 
                                    ((T(1 (fun b0 => b0) |- [0T W ~> [0TV ~> T(0 B |- idT X )0 ]0 ]0 )0)
                                       ([0TW ~> T(1 f |- X )0 ]1) (T(1 g |- X )0)).
    intros.
    compute.
    apply functional_extensionality_dep. intro.
    apply functional_extensionality_dep. intro.
    simpl. destruct x0. reflexivity.
  Qed.

  
(** written here :   (outer modification) ~~ (inner modification) **)
Lemma polyT_relT_morphism :  forall (B : obT), 
                             forall (A : obT) (A' : obT) (g : T(0 A |- A')0),
                             forall (X : obT), forall (pull : T(0 B |- A)0), forall (push : T(0 A'  |- X )0 ),
                               T(1I T(0 A' |- g )1 pull |- X )0 push
                                ~~T  T(0 X |- T(1I g |- X )0 push )1 pull .
Proof.
  (*  intros; intro; reflexivity.*)
  reflexivity.
Qed.


(** ** put any ( may be written in polymorph-style ... ) `arrows :^) logic'   V **)

      (* now: rewrite polyV_relT more generally as if enriched in T  then get old instance... therefore must rewrite polyV_relT_polymorphism more generally then get old instance
       *)

Module LOGIC.

  Set Implicit Arguments.
  Unset  Strict Implicit.
  
    Record data :=
    Data {
        obV : Type;
        polyV_relT00 : obV -> obV -> obT;
        convV : forall V1 V2, polyV_relT00 V1 V2 -> polyV_relT00 V1 V2 -> Prop;
        (* polyV_relT as primitive breaks definitional of <o and o> .. but now clearly any instance of interface V is enriched in T *)
(*        polyV_relT : forall B : obV data_of, forall (T : obT) (A : obV data_of),
                       T(0 T |- V(0 B |- A)0 )0 ->
                       forall (X : obV data_of), T(0 V(0 A |- X)0 |-  T(0 T |- V(0 B |- X)0 )0 )0;
        IdenV : forall {V : obV data_of}, V(0 V |- V )0 *)
         polyV_relT : forall (T : obT), forall B : obV,  forall (A : obV),
                       T(0 T |- (polyV_relT00 B A) )0 ->
                       forall (X : obV), T(0 (polyV_relT00 A X) |-  T(0 T |- (polyV_relT00 B X) )0 )0;
         IdenV : forall {V : obV}, (polyV_relT00 V V);
         desV00 : forall V2 : obV, forall V1 : obV, obV;
         desV10 : forall V2 : obV, forall {V1 V1'}, (polyV_relT00 V1 V1') -> (polyV_relT00 (desV00 V2 V1) (desV00 V2 V1'));
         consV00 : obV -> obV -> obV;
         consV01 : forall V1 : obV, forall {V2 V2'}, (polyV_relT00 V2 V2') -> (polyV_relT00 (consV00 V1 V2)  (consV00 V1 V2'));
         consV10 : forall {V1' V1}, (polyV_relT00 V1' V1) -> forall V2 : obV, (polyV_relT00 (consV00 V1 V2) (consV00 V1' V2));
         Des : forall {V : obV}, forall {U W : obV}, (polyV_relT00 U (consV00 V W)) -> (polyV_relT00 (desV00 V U) W);
         Cons : forall {V : obV}, forall {U W : obV}, (polyV_relT00 (desV00 V U) W) -> (polyV_relT00 U (consV00 V W));
         IdenObV : obV;
         unitV : forall {A : obV}, (polyV_relT00 IdenObV (consV00 A A) );
         Assoc : forall {V W :obV}, forall {U: obV}, (polyV_relT00 (desV00 (desV00 W V) U )  ((desV00 W (desV00  V U ))  ) );
        }.

    Arguments Des {_} {_ _ _} _ .
    Arguments Cons {_} {_ _ _} _ .
    Arguments Assoc {_} {_ _ _}.
    
    Notation "v2 ~~ v1" := (convV v2 v1)  (at level 70).
  Notation "V(0 B |- A )0" := (polyV_relT00 B A) (at level 35).
  Notation "1" := (@IdenV _ _) (at level 0).
  Notation  "(0 V1 * V2 )0" := (desV00 V2 V1) (at level 30, V1 at next level).
  Notation  "(1 v * V2 )0" := (desV10 V2 v) (at level 30, v at next level).
  Notation "[0 V1 ~> V2 ]0" := (consV00 V1 V2) (at level 30).
  Notation "[0 V1 ~> v ]1" := (consV01 V1 v) (at level 30).
  Notation "[1 v ~> V2 ]0" := (consV10 v V2) (at level 30).
  Notation  "'I'" := (@IdenObV _) (at level 0).
  Notation "'uV'" := (@unitV _) (at level 0).
  Module Ex_Notations.
    Notation "v2 ~~ dat ` v1" := (@convV dat _ _ v2 v1)  (at level 70, dat at next level, format "v2  ~~ dat `  v1").
    Notation "dat .-V(0 B |- A )0" := (@polyV_relT00 dat B A) (at level 35, format "dat .-V(0  B  |-  A  )0").
    Notation "dat .-1" := (@IdenV dat _ _) (at level 0, format "dat .-1").
    Notation  "dat .-(0 V1 * V2 )0" := (@desV00 dat V2 V1) (at level 30, V1 at next level, format "dat .-(0  V1  *  V2  )0").
    Notation  "dat .-(1 v * V2 )0" := (@desV10 dat V2 _ _ v) (at level 30, v at next level, format "dat .-(1  v  *  V2  )0").
    Notation "dat .-[0 V1 ~> V2 ]0" := (@consV00 dat V1 V2) (at level 30, format "dat .-[0  V1  ~>  V2  ]0").
    Notation "dat .-[0 V1 ~> v ]1" := (@consV01 dat V1 _ _ v) (at level 30, format "dat .-[0  V1  ~>  v  ]1").
    Notation "dat .-[1 v ~> V2 ]0" := (@consV10 dat _ _ v V2) (at level 30, format "dat .-[1  v  ~>  V2  ]0").
    Notation  "dat .-I" := (@IdenObV dat _) (at level 0, format "dat .-I").
    Notation "dat .-uV" := (@unitV dat _) (at level 0, format "dat .-uV").
  End Ex_Notations.

   (* 
    Notation "v2 ~~ dat ` v1" := (@convV dat _ _ v2 v1)  (at level 70, dat at next level, format "v2  ~~ dat `  v1").
    Notation "dat .-V(0 B |- A )0" := (@polyV_relT00 dat B A) (at level 35, format "dat .-V(0  B  |-  A  )0").
    Notation "dat .-1" := (@IdenV dat _) (at level 0, format "dat .-1").
    Notation  "dat .-(0 V1 * V2 )0" := (@desV00 dat V2 V1) (at level 30, V1 at next level, format "dat .-(0  V1  *  V2  )0").
    Notation  "dat .-(1 v * V2 )0" := (@desV10 dat V2 _ _ v) (at level 30, v at next level, format "dat .-(1  v  *  V2  )0").
    Notation "dat .-[0 V1 ~> V2 ]0" := (@consV00 dat V1 V2) (at level 30, format "dat .-[0  V1  ~>  V2  ]0").
    Notation "dat .-[0 V1 ~> v ]1" := (@consV01 dat V1 _ _ v) (at level 30, format "dat .-[0  V1  ~>  v  ]1").
    Notation "dat .-[1 v ~> V2 ]0" := (@consV10 dat _ _ v V2) (at level 30, format "dat .-[1  v  ~>  V2  ]0").
    Notation  "dat .-I" := (@IdenObV dat) (at level 0, format "dat .-I").
    Notation "dat .-uV" := (@unitV dat _) (at level 0, format "dat .-uV").

    Notation "v2 ~~ v1" := (v2 ~~ _ ` v1)  (at level 70).
    Notation "V(0 B |- A )0" := (_ .-V(0 B |- A )0) (at level 35).
    Notation "1" := (_ .-1) (at level 0).
    Notation  "(0 V1 * V2 )0" := (_ .-(0 V1 * V2 )0) (at level 30, V1 at next level).
    Notation  "(1 v * V2 )0" := (_ .-(1 v * V2 )0) (at level 30, v at next level).
    Notation "[0 V1 ~> V2 ]0" := (_ .-[0 V1 ~> V2 ]0) (at level 30).
    Notation "[0 V1 ~> v ]1" := (_ .-[0 V1 ~> v ]1) (at level 30).
    Notation "[1 v ~> V2 ]0" := (_ .-[1 v ~> V2 ]0) (at level 30).
    Notation  "'I'" := (_ .-I) (at level 0).
    Notation "'uV'" := (_ .-uV) (at level 0).
*)

  (*
  Record data :=
    Data {
        obV : Type;
        polyV_relT00 : obV -> obV -> obT;
        convV : forall V1 V2, polyV_relT00 V1 V2 -> polyV_relT00 V1 V2 -> Prop;
      }.

  Notation "v2 ~~ v1" := (convV v2 v1)  (at level 70).
  Notation "V(0 B |- A )0" := (polyV_relT00 B A) (at level 35).

  Record data1 :=
    Data1 {
        data_of :> data;
        (* polyV_relT as primitive breaks definitional of <o and o> .. but now clearly any instance of interface V is enriched in T *)
        polyV_relT : forall B : obV data_of, forall (T : obT) (A : obV data_of),
                       T(0 T |- V(0 B |- A)0 )0 ->
                       forall (X : obV data_of), T(0 V(0 A |- X)0 |-  T(0 T |- V(0 B |- X)0 )0 )0;
        IdenV : forall {V : obV data_of}, V(0 V |- V )0
      }.
*)
  
  (* TODO: below everywhere change polyV_relT to polyV_relT *)
  (*
Parameter polyV_relT_unitary : forall (B : obV), forall (A : obV),
                             V(0 B |- A )0 -> forall X : obV, V(0 A |- X )0  -> V(0 B |- X )0.
   *)
  (** almost same as the common unitary .. but no unit-picking mentionned **)
  Definition polyV_relT_unitary {log: data} : forall (B : obV log), forall (A : obV log),
                                                V(0 B |- A )0 -> forall X : obV log, T(0 V(0 A |- X )0  |- V(0 B |- X )0 )0
    := (fun (B A : obV log) (f : V(0 B |- A )0) (X : obV log) (g : V(0 A |- X )0) =>
         polyV_relT (fun _ : unit => f) g tt) .

  (** definitionally: relation of polyV_relT_identitary to polyV_relT_unitary , instead of going through polyF_relT which gives only propositional equality **)
  (*Definition polyV_relT_identitary : forall (B : obV), forall (A : obV),
                    forall X : obV, V(0 A |- X )0  -> V(0 B |- A )0 -> V(0 B |- X )0
  :=  fun (B : obV) => fun (A : obV) =>
                     fun X : obV =>  fun (a : V(0 A |- X )0) => fun (b : V(0 B |- A )0) =>
                                                           (@polyV_relT_unitary B A b X a).
   *)
  Definition polyV_relT_identitary {log : data} : forall (B : obV log), forall (A : obV log),
                                                   forall X : obV log, T(0 V(0 A |- X )0  |- T(0 V(0 B |- A )0 |- V(0 B |- X )0 )0 )0
    :=  fun (B : obV log) => fun (A : obV log) =>
                           fun X : obV log =>  fun (a : V(0 A |- X )0) => fun (b : V(0 B |- A )0) =>
                                                                     @polyV_relT log (V(0 B |- A )0) B A (fun b0 => b0) X a b .
  
  Notation "V(1 b |- X )0" := (@polyV_relT _ _ _ _ b X) (at level 35).

  Notation "V(1I b |- - )0" := (@polyV_relT_unitary _ _ _ b) (at level 35).
  (**  more precisely ( ( b 0 ) o> _ )   **)
  Notation "V(1I b |- X )0" := (@polyV_relT_unitary _ _ _ b X) (at level 35).
  (**  more precisely ( ( b 0 ) o> a )  **)
  Notation "b o> a" := (@polyV_relT_unitary _ _ _ b _ a) (at level 33, right associativity).

  Notation "V(1 'id' |- X )0" := (@polyV_relT_identitary _ _ _ X) (at level 35).
  Notation "V(0 X |- - )1" := (@polyV_relT_identitary _ _ _ X) (at level 35).
  (**  more precisely ( ( id _ ) o> a )  **)
  Notation "V(0 X |- a )1" := (@polyV_relT_identitary _ _ _ X a) (at level 35).
  (**  more precisely ( ( id b ) o> a )  **)
  Notation "a <o b" := (@polyV_relT_identitary _ _ _ _ a b) (at level 33, right associativity).

  Module Ex_Notations2.
      
    Notation "dat .-V(1 b |- X )0" := (@polyV_relT dat _ _ _ b X) (at level 35, format "dat .-V(1  b  |-  X  )0").

    Notation "dat .-V(1I b |- - )0" := (@polyV_relT_unitary dat _ _ b) (at level 35, format "dat .-V(1I  b  |-  -  )0").
    (**  more precisely ( ( b 0 ) o> _ )   **)
    Notation "dat .-V(1I b |- X )0" := (@polyV_relT_unitary dat _ _ b X) (at level 35, format "dat .-V(1I  b  |-  X  )0").
    (**  more precisely ( ( b 0 ) o> a )  **)
    Notation "b o> dat > a" := (@polyV_relT_unitary dat _ _ b _ a) (at level 33, right associativity, format "b  o> dat >  a").

    Notation "dat .-V(1 'id' |- X )0" := (@polyV_relT_identitary dat _ _ X) (at level 35, format "dat .-V(1  'id'  |-  X  )0").
    Notation "dat .-V(0 X |- - )1" := (@polyV_relT_identitary dat _ _ X) (at level 35, format "dat .-V(0  X  |-  -  )1").
    (**  more precisely ( ( id _ ) o> a )  **)
    Notation "dat .-V(0 X |- a )1" := (@polyV_relT_identitary dat _ _ X a) (at level 35, format "dat .-V(0  X  |-  a  )1").
    (**  more precisely ( ( id b ) o> a )  **)
    Notation "a < dat <o b" := (@polyV_relT_identitary dat _ _ _ a b) (at level 33, right associativity, format "a  < dat <o  b").
  End Ex_Notations2.
  (*
Hypothesis polyV_relT_arrow :  forall (B : obV), forall (A : obV),
                        forall (V V' : obT) (b : V' -> V),
                        forall (f : V -> V(0 B |- A )0 ) (X : obV),
                        forall (a : V(0 A |- X )0) (ttt: V'),
                          V(1 (fun v' => f (b v')) |- X )0 a ttt
                          = V(1 f |- X )0 a (b ttt).

Lemma polyV_relT_identitary_really :  forall (B : obV) , forall (A : obV) ,
                                 forall X : obV , forall (a : V(0 A |- X )0),  forall (b : V(0 B |- A )0),
                                   @polyV_relT_identitary B A X a b = @polyV_relT B (V(0 B |- A )0) A (fun b0 => b0) X a b .
Proof.
  intros.  unfold polyV_relT_identitary. unfold polyV_relT_unitary. 
  eapply polyV_relT_arrow with (f := fun b0 => b0) (b := fun _ : unit => b).
Qed.
Notation "V(0 X |- a )1" := (@polyF _ _ _ (@IdenV _) X <o (a : V(0 _ |- F[0 _ ~> X ]0 )0)) (at level 25).
   *)
  (*
Variable polyV_relT_morphism :  forall (B : obV), forall (V : obT),
                           forall (A : obV) (W : obT) (A' : obV) (g : W -> V(0 A |- A')0),
                           forall (f : V -> V(0 B |- A )0) (X : obV),
                             V(1 Des( [1 f ~> F[0 B ~> A' ]0 ]0 <o F[0 A' ~> g ]1 ) |- X)0
                              ~~  DesIn( [0 W ~> F[1 f ~> X ]0 ]1 <o F[1 g ~> X ]0 ).
   *)

  (* ERASE OLD: note the stronger relation (of the Coq ultimate meta logic T) ~~T instead of particular subject logic relation ~~ *)
  (*
Hypothesis polyV_relT_arrow :  forall (B : obV), forall (A : obV),
                        forall (V V' : obT) (b : V' -> V),
                        forall (f : V -> V(0 B |- A )0 ) (X : obV),
                        forall (a : V(0 A |- X )0) (ttt: V'),
                          V(1 (fun v' => f (b v')) |- X )0 a ttt
                          = V(1 f |- X )0 a (b ttt).     *)
(*
    Definition convV_fun {dat : data}: forall (U1 U2 V1 V2 : obV dat), (V(0 U1 |- U2)0 -> V(0 V1 |- V2)0) -> (V(0 U1 |- U2)0 -> V(0 V1 |- V2 )0) -> Prop
      := fun  U1 U2 V1 V2 (w' w : (V(0 U1 |- U2)0 -> V(0 V1 |- V2)0)) =>
          forall u1 u2, u1 ~~ u2 -> w' u1 ~~ w u2 .
    Notation "w' ~~~ w" := (convV_fun w' w)  (at level 70).
*)
    Record extras {dat : data} :=
      Extras {
          ReflV : forall (A1 A2 : obV dat) (f : V(0 A1 |- A2 )0), f ~~ f;
          TransV : forall (A1 A2 : obV dat) , forall (uTrans f : V(0 A1 |- A2)0), uTrans ~~ f -> forall (f' : V(0 A1 |- A2)0), f' ~~ uTrans -> f' ~~ f;
          SymV : forall (A1 A2 : obV dat),  forall (f' f : V(0 A1 |- A2)0), f ~~ f' -> f' ~~ f;
          Cong_polyV_relT :   forall (V : obT) (B A : obV dat) (f f' : T(0 V |- V(0 B |- A )0 )0),
                                (forall _v : V, f' _v ~~ f _v) -> forall X : obV dat,  forall a1 a2, a1 ~~ a2 -> forall _v, V(1 f' |- X )0 a1 _v ~~ V(1 f |- X )0 a2 _v;
          polyV_relT_arrow :  forall (B : obV dat), forall (A : obV dat),
                              forall (V V' : obT) (b : V' -> V),
                              forall (f : V -> V(0 B |- A )0 ) (X : obV dat),
                              forall (a : V(0 A |- X )0), forall (ttt: V'),
                                 V(1 (fun v' => f (b v')) |- X )0 a ttt
                                 ~~   V(1 f |- X )0 a (b ttt);
(*          polyV_relT_morphism :   forall (V : obT) (B A : obV dat) (W : obT) (A' : obV dat)
                                     (g : T(0 W |- V(0 A |- A' )0 )0) (f : T(0 V |- V(0 B |- idT A )0 )0)
                                     (X : obV dat),
                                     V(1 DesT
                                         ((T(1 fun
                                                 b0 : T(0 W |- [0TV(0 B |- idT A )0 ~> V(0 B |- idT A' )0 ]0
                                                       )0 => b0 |- [0TV ~> V(0 B |- idT A' )0 ]0 )0)
                                            ([1Tf ~> V(0 B |- idT A' )0 ]0)
                                            ((T(1 fun b0 : T(0 W |- V(0 A |- A' )0 )0 => b0
                                                                                    |- [0TV(0 B |- idT A )0 ~> V(0 B |- idT A' )0 ]0 )0)
                                               (V(1 ( IdenT ) |- A' )0) g)) |- X )0 ~~T
                                      DesInT (V:=V) (U0:=V(0 A' |- X )0) (U1:=W) (W:=V(0 B |- idT X )0)
                                      ((T(1 fun b0 : T(0 V(0 A' |- X )0 |- [0TW ~> V(0 A |- X )0 ]0 )0 => b0
                                                                                                    |- [0TW ~> [0TV ~> V(0 B |- idT X )0 ]0 ]0 )0)
                                         ([0TW ~> V(1 f |- X )0 ]1) (V(1 g |- X )0)); *)
  (*        polyV_relT_morphism :   forall (V : obT) (B A : obV dat) (W : obT) (A' : obV dat)
                                    (g : T(0 W |- V(0 A |- A' )0 )0) (f : T(0 V |- V(0 B |- idT A )0 )0)
                                    (X : obV dat),
                                    V(1 DesT( ([1Tf ~> V(0 B |- idT A' )0 ]0) <<o (V(0 A' |- g )1)) |- X )0 ~~T
                                     DesInT( ([0TW ~> V(1 f |- X )0 ]1) <<o (V(1 g |- X )0) );
*)
          (** written here :   (outer modification) ~~ (inner modification) **)
          polyV_relT_morphism :  forall (B : obV dat), 
                                 forall (A : obV dat) (A' : obV dat) (g : V(0 A |- A')0),
                                 forall (X : obV dat), forall (pull : V(0 B |- A)0), forall (push : V(0 A'  |- X )0 ),
                                    V(1I V(0 A' |- g )1 pull |- X )0 push
                                    ~~ V(0 X |- V(1I g |- X )0 push )1 pull;
          (** ALT 
Hypothesis Cong_polyV_relT : forall (B : obV), forall (A : obV),
                       forall X : obV, forall (a a' : V(0 A |- X )0),
                         a' ~~ a -> @polyV_relT_identitary B A X a' ~~~ @polyV_relT_identitary B A X a .
           **)
          (** related to non-variance when unit pull the input, commonly  ( 1 o> h ) ~~ h  **)
          polyV_relT_unitV : forall (A : obV dat), forall X : obV dat,  forall a1 a2, a1 ~~ a2 -> ( @idT (V(0 A |- X )0)  ) a1 ~~ ( V(1I (@IdenV _ A) |- X )0 ) a2;
          (** related to non-variance when unit push the output, commonly  ( (f _i) o> 1 ) ~~ (f _i)  , 
       therefore polyV is injective **)
          polyV_relT_inputUnitV : forall (B : obV dat), forall (A : obV dat),
                              forall (b : V(0 B |- A )0),
                                b  ~~ ( (V(1I b |- A )0)  (@IdenV _ A) );
          
          CongDes : forall V : obV dat, forall (U W : obV dat), forall (f f' : V(0 U |- [0 V ~> W ]0 )0),
                      f' ~~ f -> Des f' ~~ Des f ;
          Des_Cons : forall V : obV dat, forall (U W : obV dat), forall (f : V(0 (0 U * V )0 |-  W )0),
                       Des (Cons f) ~~ f ;
          Des_Output : forall V : obV dat, forall (U W : obV dat), forall (v : V(0 U |- [0 V ~> W ]0 )0), forall W' (w : V(0 W |- W' )0),
                                  Des( [0 V ~> w ]1 <o v ) ~~ w <o Des( v ) ;
          CongCons : forall V : obV dat, forall (U W : obV dat), forall (v v' : V(0 (0 U * V )0 |- W )0 ),
                       v' ~~ v -> Cons v' ~~ Cons v ;
          Cons_Des : forall V : obV dat, forall (U W : obV dat), forall (f : V(0 U |-  [0 V ~> W ]0 )0),
                       Cons (Des f) ~~ f ;
          Cons_Input : forall V : obV dat, forall (U U' : obV dat) (w : V(0 U' |- U )0), forall (W : obV dat) (v : V(0 (0 U * V )0 |- W )0),
                         Cons(v <o (1 w * V )0 )  ~~ Cons( v ) <o w ;

        }.

    Arguments ReflV {_ _} _ _ _ .
    Arguments TransV {_ _} _ _ _ _ _ _ _ .
    Arguments SymV {_ _} _ _ _ _ _ . About Cong_polyV_relT.
    Arguments Cong_polyV_relT {_ _} [_ _ _ _ _ _ _ _]  _ _ _ .
    Arguments polyV_relT_arrow {_ _} _ _ _ _ _ _ _ _ _ .
    Arguments polyV_relT_morphism {_ _} _ _ _ _ _ _ _ .
    Arguments polyV_relT_unitV {_ _} _ _ _ _ _ . 
    Arguments polyV_relT_inputUnitV {_ _} _ _ _ .
    Arguments CongDes {_ _} [_ _ _ _ _] _ .
    Arguments Des_Cons {_ _} [_ _ _] _ .
    Arguments Des_Output {_ _} [_ _ _ _ _] _ .
    Arguments CongCons {_ _} [_ _ _] _ _ _.
    Arguments Cons_Des {_ _} [_ _ _ _] .
    Arguments Cons_Input {_ _} [_ _ _ _ _] _ .
(*    Arguments DesIn {_ _} [_ _ _ _] _ .
    Arguments DesIdenObR {_ _} [_ _] _  .
    Arguments CongDesIdenObR {_ _} [_ _ _ _] _  .
    Arguments DesIdenObR_output {_ _} [_ _ _] _ _ .
    Arguments DesIdenObL {_ _} [_ _] _  .
    Arguments ConsIdenObL {_ _} [_ _] _  .
    Arguments ConsIdenObL_DesIdenObL {_ _} [_ _] _ . 
    Arguments CongConsIdenObL {_ _} [_ _ _ _] _ .
    Arguments consV10_functorial {_ _} [_ _ _] _  _ _ .
    Arguments consV11_bifunctorial {_ _} [_ _ _ _] _ _ .
    Arguments CongConsV10 {_ _} [_ _ _ _] _ _ .
*)    

    Lemma           polyV_relT_morphism'' {dat : data} {ext : @extras dat} :  forall (B : obV dat), 
                                 forall (A : obV dat) (A' : obV dat) (g : V(0 A |- A')0),
                                 forall (X : obV dat), forall (pull : V(0 B |- A)0), forall (push : V(0 A'  |- X )0 ),
                                    V(1I V(0 A' |- g )1 pull |- X )0 push
                                    ~~ V(0 X |- V(1I g |- X )0 push )1 pull.
      Check           polyV_relT_morphism .
      Abort.
    Lemma Cong_polyV_relT' {dat : data} {ext : @extras dat} : forall (B : obV dat), forall (A : obV dat),
                                          forall (f f' : V(0 B |- A )0),
                               f' ~~ f -> forall X : obV dat,
                                            forall a1 a2, a1 ~~ a2 -> @polyV_relT_unitary dat B A f' X a1 ~~  @polyV_relT_unitary _ B A f X a2.
    Proof.
      intros. eapply  (@Cong_polyV_relT _ ext)  with (f:=fun _ : unit => f)  (f':=fun _ : unit => f'); intros; assumption.
    Qed.
    Arguments Cong_polyV_relT' {_ _} [_ _ _ _ _ _ _] _ _ .
                                             
    Structure logic :=
      Logic {
          data_of :> data;
          extras_of :> @extras data_of
        }.

    (* not critical, only for easy proofs without doing (extras_of _) *)
    Existing Class extras. 
    Existing Instance extras_of. 

    Section Context.
      Context {log : logic}.
            
      Lemma polyV_relT_unitary_rel_identitary :  forall (B : obV log) , forall (A : obV log) ,
                                                              forall X : obV log , forall (a : V(0 A |- X )0),  forall (b : V(0 B |- A )0),
                                                                @polyV_relT_unitary log B A b X a  ~~  a <o b . (* @polyV_relT B (V(0 B |- A )0) A (fun b0 => b0) X a b .*)
      Proof.
        unfold polyV_relT_identitary. unfold polyV_relT_unitary.
        intros.  eapply (@polyV_relT_arrow log log) with (f := fun b0 => b0) (b := fun _ : unit => b).
      Qed.

      Definition ComV : forall (V1 : obV log), forall UCom, V(0 V1 |-  UCom )0 -> forall V3, V(0 UCom |- V3 )0 -> V(0 V1 |- V3 )0 := polyV_relT_unitary .

      Lemma CongCom : forall (A2 A3 : obV log), forall (f2 f2' : V(0 A2 |- A3 )0), f2 ~~ f2' -> forall A1, forall (f1 f1' : V(0 A1 |- A2 )0), f1 ~~ f1' -> f2 <o f1 ~~ f2' <o f1'.
      Proof.
(*        intros. do 2 rewrite <- (polyV_relT_unitary_rel_identitary ) by exact tt. Check Cong_polyV_relT'.
        pose (dd:=@Cong_polyV_relT' log log). unfold convT in dd.
                                                     
        erewrite Cong_polyV_relT' with  (f':=fun _ : unit =>  f2').  apply Cong_polyV_relT'.
        assumption.
        assumption. *)
        intros. eapply TransV; [ eapply polyV_relT_unitary_rel_identitary | ].
        eapply TransV; [| eapply SymV, polyV_relT_unitary_rel_identitary].
        apply Cong_polyV_relT';  assumption.
      Qed.

      Lemma Cat2V : forall (A3 A4 : obV log) (f3 : V(0 A3 |- A4)0), forall A2 (f2 : V(0 A2 |- A3)0), forall A1 (f1 : V(0 A1 |- A2)0),
                      (f3 <o f2) <o f1 ~~ f3 <o (f2 <o f1).
      Proof.
(*        intros. apply SymV.   About  polyV_relT_unitary_rel_identitary. About monoV_morphism.
        replace ( f3 <o ( f2 <o f1) ) with    ((f2 <o f1) o> f3) by (apply  polyV_relT_unitary_rel_identitary; exact tt).
        replace  (f3 <o f2) with  (f2 o> f3) by (apply  polyV_relT_unitary_rel_identitary; exact tt).
        apply polyV_relT_morphism . *)
        (* OLD DEFINITIONALLY intros. apply SymV, monoV_morphism. *)
        intros. eapply TransV; [ eapply polyV_relT_unitary_rel_identitary  |].
        eapply TransV; [| eapply CongCom; [|eapply ReflV]; eapply SymV, polyV_relT_unitary_rel_identitary  ].
        apply SymV, polyV_relT_morphism.
      (*replace ( f3 <o ( f2 <o f1) ) with    ((f2 <o f1) o> f3) by (apply  polyV_relT_unitary_rel_identitary; exact tt).
  replace  (f3 <o f2) with  (f2 o> f3) by (apply  polyV_relT_unitary_rel_identitary; exact tt). *)
        (* OLD DEFINITIONALLY intros. apply SymV, polyV_relT_morphism. *) 
      Qed.

      Lemma Cat1RightV : forall (A1 A2 : obV log), forall f : V(0 A1 |- A2)0,  f ~~ f <o 1.
      Proof.
(*        intros. do 1 rewrite <- polyV_relT_unitary_rel_identitary by exact tt. apply polyV_relT_unitV.
        apply ReflV. *)
       intros. eapply TransV; [ eapply polyV_relT_unitary_rel_identitary |].
        apply polyV_relT_unitV.
        apply ReflV.
      Qed.
      
      Lemma Cat1LeftV : forall (A1 A2 : obV log), forall f : V(0 A1 |- A2)0,  f ~~ 1 <o f.
      Proof.
(*        intros. do 1 rewrite <- polyV_relT_unitary_rel_identitary by exact tt. apply polyV_relT_inputUnitV. *)
        intros. eapply TransV; [ eapply polyV_relT_unitary_rel_identitary |].
        apply polyV_relT_inputUnitV. 
      Qed.

      (** later, most of the remaining fields shall be DEFINITIONS and LEMMAS **)
      Definition DesIn : forall {V : obV log}, forall {U0 U1 W : obV log}, V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0 -> V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0.
        intros. apply Cons. eapply polyV_relT_identitary. Check @Assoc. 2: eapply (@Assoc log _ _ _).  eapply Des.
        eapply Des. exact H.
        Defined.
      Axiom CongDesIn : forall V : obV log, forall (U0 U1 W : obV log), forall (v v' : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0),
                          v' ~~ v -> DesIn v' ~~ DesIn v.
      Parameter ConsIn : forall V : obV log, forall (U0 U1 W : obV log), V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0 -> V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0 .
      Axiom CongConsIn : forall V : obV log, forall (U0 U1 W : obV log), forall (v v' : V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0),
                           v' ~~ v -> ConsIn v' ~~ ConsIn v .
      Axiom ConsIn_DesIn : forall V : obV log, forall (U0 U1 W : obV log), forall (f : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0),
                             ConsIn (DesIn f) ~~ f .
      Axiom DesIn_Input : forall V : obV log, forall (U0 U1 W : obV log), forall (v : V(0 U0 |- [0 U1 ~> [0 V ~> W ]0 ]0 )0), forall (U0' : obV log) (i : V(0 U0' |- U0 )0),
                            (DesIn v) <o i ~~ DesIn( v <o i ) .
      Parameter polyV_relV : forall (W : obV log), forall (U : obV log) (V : obV log),
                               V(0 U |- [0 W ~> V ]0 )0 ->
                               forall X : obV log, V(0 [0 V ~> X ]0  |- [0 U ~> [0 W ~> X ]0 ]0 )0 .
      Axiom polyV_relV_polyV_relT : forall (W : obV log), forall (U : obV log) (V : obV log),
                                    forall (v : V(0 U |- [0 W ~> V ]0 )0), forall X : obV log,
                                      [1 Des v ~> X]0
                                                    ~~ DesIn( polyV_relV v X ) .
      Axiom polyV_relV_arrow :  forall (B : obV log) (A : obV log) (V : obV log),
                                forall (V' : obV log) (v : V(0 V' |- V )0),
                                forall (f : V(0 V |- [0 B ~> A ]0 )0) (X : obV log),
                                  polyV_relV (f <o v) X
                                             ~~ [1 v ~> [0 B ~> X ]0 ]0 <o (polyV_relV f  X) .
    End Context.

    Notation "V[0 U ~> V ]0" := ([0 U ~> V ]0) (at level 25, only parsing).
    Notation "V[1 v ~> X ]0" := (@polyV_relV _ _ _ _ v X) (at level 25).
    Notation "V[0 X ~> w ]1" := (@polyV_relV _ _ _ _ 1 X <o w) (at level 25).
    Notation "V[0 W ~> - ]1" := (fun V X => @polyV_relV _ _ _ _ (@IdenV _ ([0 W ~> V ]0)) X) (at level 25). 

    Section Context2.
          Context {log : logic}.

          Parameter DesIdenObR : forall {U W : obV log}, V(0 U |- [0 I ~> W ]0 )0 -> V(0 U  |- W )0 .
          Axiom CongDesIdenObR : forall (U W : obV log), forall (v v' : V(0 U |- [0 I ~> W ]0 )0),
                                   v' ~~ v -> DesIdenObR v' ~~ DesIdenObR v .
          Axiom DesIdenObR_output : forall (U : obV log) (W W' : obV log) (w : V(0 W |- W' )0), forall v : V(0 U |- [0 I ~> W ]0 )0, 
                                      DesIdenObR( [0 I ~> w ]1 <o v ) ~~ w <o DesIdenObR( v ) .
          Parameter DesIdenObL : forall {V : obV log}, forall {W : obV log}, V(0 I |- [0 V ~> W ]0 )0 -> V(0 V |- W )0 .
          Parameter ConsIdenObL : forall V : obV log, forall (W : obV log), V(0 V |- W )0 -> V(0 I |- [0 V ~> W ]0 )0 .
          Axiom ConsIdenObL_DesIdenObL : forall V : obV log, forall (W : obV log), forall v : V(0 I |- [0 V ~> W ]0 )0,
                                           v ~~ ConsIdenObL( DesIdenObL v) .
          Axiom CongConsIdenObL : forall V : obV log, forall (W : obV log), forall (v v' : V(0 V |- W )0),
                                    v' ~~ v -> ConsIdenObL v' ~~ ConsIdenObL v .
          Axiom consV10_functorial : forall (V1' V1 : obV log) (v :  V(0 V1' |- V1 )0), forall V1'' (v' : V(0 V1'' |- V1' )0), forall V2 : obV log,
                                       [1 v <o v' ~> V2 ]0 ~~  [1 v' ~> V2 ]0 <o  [1 v ~> V2 ]0 .
          Axiom consV11_bifunctorial : forall (V1' V1 : obV log) (v : V(0 V1' |- V1 )0), forall W1 W1' (w : V(0 W1 |- W1' )0),
                                         [0 V1' ~> w ]1 <o  [1 v ~> W1 ]0 ~~ [1 v ~> W1' ]0 <o [0 V1 ~> w ]1 .
          Axiom CongConsV10 : forall (V1' V1 : obV log) (v v' : V(0 V1' |- V1)0), forall V2 : obV log,
                                v' ~~ v -> [1 v' ~> V2 ]0 ~~ [1 v ~> V2 ]0 .
    End Context2.

    Canonical Structure logT : logic :=
      @Logic _
            (@Extras (Data (polyV_relT00:=polyT_relT00) convT polyT_relT 
                  (@IdenT) (desV00:=desT00) desT10 (consV00:=consT00) consT01 consT10 DesT
                  ConsT  (@unitT) (@AssocT)) ReflT TransT SymT Cong_polyT_relT polyT_relT_arrow
                    polyT_relT_morphism polyT_relT_unitT polyT_relT_inputUnitT CongDesT
                    Des_ConsT Des_OutputT CongConsT Cons_DesT Cons_InputT).
    Print logT.
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
    Existing Class data.
    
  End Context.
(*
  Definition obA {log : logic} {obA obB : Type} {polyF0 : obA -> obB} (dat : @data1 log obA obB polyF0) := obA.
  Definition obB {log : logic} {obA obB : Type} {polyF0 : obA -> obB} (dat : @data1 log obA obB polyF0) := obB.
  Definition polyF0 {log : logic} {obA obB : Type} {polyF0 : obA -> obB} (dat : @data1 log obA obB polyF0) := polyF0.
 *)

  Notation "A[0 A1 ~> A2 ]0" := (@polyA00 _ _ A1 A2) (at level 25).
(*  Notation "A[0 A1 ~> A2 ]0" := ((_.-A[0 A1 ~> A2 ]0)%mys) (at level 25).*)
  (** therefore "A[1 f ~> X ]0" is similar to ( f o> _ ) **)
  (*  Notation "A[1 f ~> X ]0" := (@polyA _ _ _ _ _ f X) (at level 25).*)
  Notation "A[1 f ~> X ]0" := (@polyA _ _ _ _ _ f X) (at level 25).
  (** therefore "A[0 X ~> g ]1" is similar to the common ( _ <o g ) **)
  Notation "A[0 X ~> g ]1" := (@polyA _ _ _ _ _ (@IdenV _ _) X <o (g : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).
  Notation "'uA'" := (@unitA _ _ _) (at level 0).
  
    Notation "B[0 B1 ~> B2 ]0" := (@polyB00 _ _ B1 B2) (at level 25).
    (** therefore "B[1 m ~> Y ]0" is similar to ( m o> _ ) **)
    Notation "B[1 m ~> Y ]0" := (@polyB _ _ _ _ _ m Y) (at level 25).
    (** therefore "B[0 Y ~> n ]1" is similar to the common ( _ <o n ) **)
    Notation "B[0 Y ~> n ]1" := (@polyB _ _ _ _ _ (@IdenV _ _) Y <o (n : V(0 _ |- B[0 _ ~> Y ]0 )0)) (at level 25).

    Module Ex_Notations3.
      Notation "dat .-A[0 A1 ~> A2 ]0" := (@polyA00 _ dat A1 A2) (at level 25).
      Notation "A[0 A1 ~> A2 ]0" := (_  .-A[0 A1 ~> A2 ]0) (at level 25).
      (*  Notation "A[0 A1 ~> A2 ]0" := ((_.-A[0 A1 ~> A2 ]0)%mys) (at level 25).*)
      (** therefore "A[1 f ~> X ]0" is similar to ( f o> _ ) **)
      (*  Notation "A[1 f ~> X ]0" := (@polyA _ _ _ _ _ f X) (at level 25).*)
      Notation "dat .-A[1 f ~> X ]0" := (@polyA _ dat _ _ _ f X) (at level 25).
      Notation "A[1 f ~> X ]0" := (_.-A[1 f ~> X ]0) (at level 25).
      (** therefore "A[0 X ~> g ]1" is similar to the common ( _ <o g ) **)
      Notation "dat .-A[0 X ~> g ]1" := (@polyA _ dat _ _ _ (@IdenV _ _) X <o (g : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).
      Notation "A[0 X ~> g ]1" := (_.-A[0 X ~> g ]1) (at level 25).
      Notation "dat .-uA" := (@unitA _ dat _) (at level 0).
      
      Notation "dat .-B[0 B1 ~> B2 ]0" := (@polyB00 _ dat B1 B2) (at level 25).
      Notation "B[0 B1 ~> B2 ]0" := (_.-B[0 B1 ~> B2 ]0) (at level 25).
      (** therefore "B[1 m ~> Y ]0" is similar to ( m o> _ ) **)
      Notation "dat .-B[1 m ~> Y ]0" := (@polyB _ dat _ _ _ m Y) (at level 25).
      Notation "B[1 m ~> Y ]0" := (_.-B[1 m ~> Y ]0) (at level 25).
      (** therefore "B[0 Y ~> n ]1" is similar to the common ( _ <o n ) **)
      Notation "dat .-B[0 Y ~> n ]1" := (@polyB _ dat _ _ _ (@IdenV _ _) Y <o (n : V(0 _ |- B[0 _ ~> Y ]0 )0)) (at level 25).
      Notation "B[0 Y ~> n ]1" := (_.-B[0 Y ~> n ]1) (at level 25).
    End Ex_Notations3.
    
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

    Notation "A[0 B ~> - ]1" := (@polyA_IdenV _ _ B) (at level 25).
    Notation "B[0 B ~> - ]1" := (@polyB_IdenV _ _ B) (at level 25).
    
    Notation "F|0 A" := (@polyF0 _ _ A) (at level 4, right associativity).
    (** :^) **)
    Notation "F[0 B ~> A ]0" := (B[0 B ~> F|0 A ]0) (at level 25).
    (** therefore "F[1 b ~> X ]0" is similar to   ( b o> ( F|1 _ ) )   , alternatively   ( b o>F _ )   **)
    Notation "F[1 b ~> X ]0" := (@polyF _ _ _ _ _ b X) (at level 25).
    (** therefore "F[0 X ~> a ]1" is similar to   ( B[0 B ~> ( F|1 a ) ]1 ) which is ( _ o> ( F|1 a ) )   , alternatively  ( _ o>F a )   **)
    Notation "F[0 X ~> a ]1" := (@polyF _ _ _ _ _ (@IdenV _ _) X <o (a : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).

    Module Ex_Notations4.
      Export Ex_Notations3.
      Notation "dat .-A[0 B ~> - ]1" := (@polyA_IdenV _ dat B) (at level 25, format  "dat .-A[0  B  ~>  -  ]1").
      Notation "dat .-B[0 B ~> - ]1" := (@polyB_IdenV _ dat B) (at level 25, format "dat .-B[0  B  ~>  -  ]1").
      
      Notation "dat .-F|0 A" := (@polyF0 _ dat A) (at level 4, right associativity, format "dat .-F|0  A").
      (** :^) **)
      Notation "dat .-F[0 B ~> A ]0" := (dat.-B[0 B ~> (dat.-F|0 A) ]0) (at level 25, format "dat .-F[0  B  ~>  A  ]0").
      (** therefore "F[1 b ~> X ]0" is similar to   ( b o> ( F|1 _ ) )   , alternatively   ( b o>F _ )   **)
      Notation "dat .-F[1 b ~> X ]0" := (@polyF _ dat _ _ _ b X) (at level 25, format "dat .-F[1  b  ~>  X  ]0").
      (** therefore "F[0 X ~> a ]1" is similar to   ( B[0 B ~> ( F|1 a ) ]1 ) which is ( _ o> ( F|1 a ) )   , alternatively  ( _ o>F a )   **)
      Notation "dat .-F[0 X ~> a ]1" := (@polyF _ dat _ _ _ (@IdenV _ _) X <o (a : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25, format "dat .-F[0  X  ~>  a  ]1").
    End Ex_Notations4.
    
    Section Context3.
      Context {log : logic}.
      Context {dat : @data log}.

      Definition polyF_IdenV : forall (B : obB dat) (A : obA dat),
                               forall X : obA dat, V(0 A[0 A ~> X ]0  |- [0 F[0 B ~> A ]0 ~> F[0 B ~> X ]0 ]0 )0
        := (fun B A X => @polyF _ _ (F[0 B ~> A ]0) B A (@IdenV _ (F[0 B ~> A ]0)) X).
      
    End Context3.
    Notation "dat .-F[0 B ~> - ]1" := (@polyF_IdenV _ dat B) (at level 25).
    Notation "F[0 B ~> - ]1" := (_.-F[0 B ~> - ]1) (at level 25).

    Section Context4.
      Context {log : logic}.
      
      Record extras (dat : @data log) :=
        Extras {
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
                               F[1 Des( [1 f ~> F[0 B ~> A' ]0 ]0 <o F[0 A' ~> g ]1 ) ~> X]0
                                ~~  DesIn( [0 W ~> F[1 f ~> X ]0 ]1 <o A[1 g ~> X ]0 );
            CongPolyF : forall (V : obV log) (B : obB dat) (A : obA dat),
                         forall (f f' : V(0 V |- F[0 B ~> A ]0 )0),
                           f' ~~ f -> forall X : obA dat, polyF f' X ~~ polyF f X;
            polyA_unitA : forall (A : obA dat), forall X : obA dat, (@IdenV _ (A[0 A ~> X ]0)) ~~ DesIdenObR( A[1 (@unitA _ dat A) ~> X ]0 );
            polyA_inputUnitA : forall (V : obV log), forall (B : obA dat), forall (A : obA dat),
                               forall (f : V(0 V |- A[0 B ~> A ]0 )0),
                                 f  ~~ DesIdenObL( (A[1 f ~> A ]0) <o (@unitA _ dat A) );
            polyF_inputUnitA : forall (V : obV log) (B : obB dat) (A : obA dat),
                               forall (f : V(0 V |- F[0 B ~> A ]0 )0),
                                 f ~~ DesIdenObL( (F[1 f ~> A ]0) <o (@unitA _ dat A) )
          }.

      Existing Class extras. About polyA_arrow.
      Global Arguments CongPolyA {_ _} [_ _ _ _ _] _ _  .
      Global Arguments polyA_arrow {_ _} [_ _ _ _] _ _ _ .
      Global Arguments polyF_arrow {_ _} [_ _ _ _] _ _  _ .
      Global Arguments polyF_morphism {_ _} [_ _ _ _ _] _ _ _ .
      Global Arguments CongPolyF {_ _} [_ _ _ _ _] _ _ . About polyF_inputUnitA.
      Global Arguments polyA_unitA {_ _} _ _ .
      Global Arguments polyA_inputUnitA {_ _} [_ _ _] _ .
      Global Arguments polyF_inputUnitA {_ _} [_ _ _] _  .

    End Context4.

    Coercion dat {log : logic} {dat : @data log} (ext : @extras log dat) := dat.

    Section Context5.
      Variable (log : logic).

      Structure functor :=
        Functor {
            data_of :> @data log;
            extras_of :> @extras _ data_of
          }.

      (* not critical, only for easy proofs without doing (extras_of _) *)
      Global Existing Instance extras_of. 
    End Context5.

    Section Context8.
      Context {log : logic}.
      Context {dat_ : @data log}.
      Context {func : @extras _ dat_}.

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
                            forall (C X : obA func),
                              ( [0 A[0 A ~> C ]0 ~> F[1 f ~> X ]0 ]1
                                <o A[0 A ~> - ]1 C X )
                                ~~ ( [1 F[1 f ~> C ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
                                     <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) .
      Proof.
        (* enough ( DesIn( _ ) ~~ DesIn( _ ) ) *)
        intros;  eapply TransV; [ eapply TransV | ]; [ apply ConsIn_DesIn | idtac | apply SymV, ConsIn_DesIn].
        apply CongConsIn.

        (* convert left hand side : outer polyF_morphism then inner polyF_arrow *)
        assert ( LHS1 : F[1 Des( [1 f ~> F[0 B ~> C ]0 ]0 <o F[0 C ~> (@IdenV _ (A[0 A ~> C]0)) ]1 ) ~> X ]0
                         ~~ DesIn( [0 A[0 A ~> C ]0 ~> F[1 f ~> X ]0 ]1 <o A[0 A ~> - ]1 C X ) )
          by apply polyF_morphism.

        assert ( LHS2 : F[1 Des( F[1 (@IdenV _ (F[0 B ~> A ]0)) <o f ~> C ]0 ) ~> X ]0
                         ~~ F[1 Des( [1 f ~> F[0 B ~> C ]0 ]0 <o F[0 C ~> (@IdenV _ (A[0 A ~> C ]0)) ]1 ) ~> X ]0 )
          by ( apply CongPolyF, CongDes;  eapply TransV; [ eapply Cat2V | ]; eapply TransV; [ eapply Cat1RightV | ];
               apply polyF_arrow ).

        (* convert right hand side : outer polyV_relV_arrow then outer polyF_arrowIn which is inner form of polyF_arrow *)
        assert ( RHS1 : DesIn( ( V[1 (@IdenV _ (V[0 V ~> (F[0 B ~> C ]0) ]0)) <o (F[1 f ~> C ]0) ~> (F[0 B ~> X ]0) ]0 ) <o F[0 B ~> - ]1 C X )
                             ~~ DesIn( [1 F[1 f ~> C ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0 <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) )
          by ( eapply TransV; [ eapply CongDesIn; eapply Cat2V | ];
               apply CongDesIn; apply CongCom; [ | apply ReflV];
               apply polyV_relV_arrow ).

        assert ( RHS2 : ( F[1 (@IdenV _ (F[0 B ~> C ]0)) <o Des( (@IdenV _ (V[0 V ~> (F[0 B ~> C ]0) ]0)) <o (F[1 f ~> C ]0) ) ~> X ]0 )
                          ~~ DesIn( ( V[1 (@IdenV _ (V[0 V ~> (F[0 B ~> C ]0) ]0)) <o (F[1 f ~> C ]0) ~> (F[0 B ~> X ]0) ]0 ) <o F[0 B ~> - ]1 C X ) )
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
      forall (C X : obA func),
        ( [0 A[0 A ~> C ]0 ~> β X ]1
          <o A[0 A ~> - ]1 C X )
          ~~ ( [1 β C ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
               <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) .

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
(*    Check fun log => fun cc : @category log  =>  polyF_arrowIn (func:=cc).
    Check fun log => fun cc : @category log  =>  polyF_morphism (e:= cc).*)


(*
          Record data :=
            Data {
        obV : Type;
        polyV_relT00 : obV -> obV -> obT;
        polyV_relT : forall (T : obT), forall B : obV,  forall (A : obV),
                       T(0 T |- (polyV_relT00 B A) )0 ->
                       forall (X : obV), T(0 (polyV_relT00 A X) |-  T(0 T |- (polyV_relT00 B X) )0 )0;
         IdenV : forall {V : obV}, (polyV_relT00 V V);
         desV00 : forall V2 : obV, forall V1 : obV, obV;
         desV10 : forall V2 : obV, forall V1 V1', (polyV_relT00 V1 V1') -> (polyV_relT00 (desV00 V2 V1) (desV00 V2 V1'));
         consV00 : obV -> obV -> obV;
         consV01 : forall V1 : obV, forall V2 V2', (polyV_relT00 V2 V2') -> (polyV_relT00 (consV00 V1 V2)  (consV00 V1 V2'));
         consV10 : forall V1' V1, (polyV_relT00 V1' V1) -> forall V2 : obV, (polyV_relT00 (consV00 V1 V2) (consV00 V1' V2));
         Des : forall V : obV, forall (U W : obV), (polyV_relT00 U (consV00 V W)) -> (polyV_relT00 (desV00 V U) W);
         Cons : forall V : obV, forall (U W : obV), (polyV_relT00 (desV00 V U) W) -> (polyV_relT00 U (consV00 V W));
         IdenObV : obV;
         unitV : forall {A : obV}, (polyV_relT00 IdenObV (consV00 A A) )
        }.
 *)

End FUNCTOR.

Module CATEGORY.
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
      Existing Class data.

      Coercion dataFun_of_dataCat (d : data)
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

      Global Arguments dataFun_of_dataCat : simpl never.

      Record extras {dat : data} :=
        Extras {
            CongPolyA : forall (V : obV log), forall (B : FUNCTOR.obA dat), forall (A : FUNCTOR.obA dat),
                        forall (f f' : V(0 V |- A[0 B ~> A ]0 )0),
                          f' ~~ f -> forall X : FUNCTOR.obA dat, polyA f' X ~~ polyA f X;
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
            polyA_inputUnitA : forall (V : obV log), forall (B :  FUNCTOR.obA dat), forall (A :  FUNCTOR.obA dat),
                               forall (f : V(0 V |- A[0 B ~> A ]0 )0),
                                 f  ~~ DesIdenObL( (A[1 f ~> A ]0) <o (@FUNCTOR.unitA _ dat A) );
          }.

      Existing Class extras.
      Global Arguments CongPolyA {_ _} [_ _ _ _ _] _ _  .
      Global Arguments polyA_arrow {_ _} [_ _ _ _] _ _ _ .
      Global Arguments polyF_morphism {_ _} [_ _ _ _ _] _ _ _ .
      Global Arguments polyA_unitA {_ _} _ _ .
      Global Arguments polyA_inputUnitA {_ _} [_ _ _] _ .

      Coercion extrasFun_of_extrasCat (d : data) (e : @extras  d)
      : @FUNCTOR.extras log (dataFun_of_dataCat d) := 
        {|
          FUNCTOR.CongPolyA := CongPolyA;
          FUNCTOR.polyA_arrow := polyA_arrow;
          FUNCTOR.polyF_arrow := polyA_arrow;
          FUNCTOR.polyF_morphism := polyF_morphism;
          FUNCTOR.CongPolyF := CongPolyA;
          FUNCTOR.polyA_unitA := polyA_unitA;
          FUNCTOR.polyA_inputUnitA := polyA_inputUnitA;
          FUNCTOR.polyF_inputUnitA := polyA_inputUnitA |}.

      Global Arguments extrasFun_of_extrasCat : simpl never.
      
    End Context6.

    Section Context6'.
      Structure category (log : logic) :=
        Category {
            data_of :> @data log;
            extras_of :> @extras  log (data_of)
          }.

      (* is this necessary?*)
      Global Existing Instance extras_of.

      Coercion functor_of_category {log : logic} (c : @category log)
      : @FUNCTOR.functor log :=  {| FUNCTOR.data_of := data_of c; FUNCTOR.extras_of := extras_of c |}.
      (* false ambiguity : new coercion produce same output as old coercion ; the new coercion will be used to coerce but also the notational hiddenness/implicitness of old coercion is kept for printing *)
      Canonical Structure functor_of_category.
      
    End Context6'.

    Export FUNCTOR.
End CATEGORY.

Module FUNCTORTOCAT.
  Export CATEGORY.
  Import Ex_Notations4.
  Set Implicit Arguments.
  Unset  Strict Implicit.

  Section Context.
    Context {log : logic} (from : @category log) (to : @category log).
    
    Record data :=
      Data {
        polyF0 : obA from -> obA to;
        polyF :   forall {V : obV log}{B : obA to} {A : obA from},
                    V(0 V |- to .-A[0 B ~> polyF0 A ]0 )0 ->
                    forall X : obA from,
                      V(0 from .-A[0 A ~> X ]0 |- [0V ~> to .-A[0 B ~> polyF0 X ]0 ]0 )0;
        }.

    Existing Class data.

    Record extras {dat : data} :=
      Extras {
          polyF_arrow :    forall {B : obA to} {A : obA from} {V V' : obV log} 
                           (v : V(0 V' |- V )0) (f : V(0 V |- to .-A[0 B ~> polyF0 dat A ]0 )0)
                           (X : obA from),
                           polyF  (f <o v) X ~~
                                 [1v ~> to .-A[0 B ~> polyF0 dat X ]0 ]0 <o polyF f X ;
          polyF_morphism :    forall (V : obV log) (B : obA to) (A : obA from) 
                                (W : obV log) (A' : obA from) (g : V(0 W |- from .-A[0 A ~> A' ]0 )0)
                                (f : V(0 V |- to .-A[0 B ~> polyF0 dat A ]0 )0) (X : obA from),
                                polyF 
                                      (Des
                                         ([1f ~> to .-A[0 B ~> polyF0 dat A' ]0 ]0 <o
                                                                                  polyF  1 A' <o g)) X ~~
                                      DesIn ([0W ~> polyF  f X ]1 <o from .-A[1 g ~> X ]0) ;
          CongPolyF :    forall (V : obV log) (B : obA to) (A : obA from)
                           (f f' : V(0 V |- to .-A[0 B ~> polyF0 dat A ]0 )0),
                           f' ~~ f -> forall X : obA from, polyF  f' X ~~ polyF f X;
          polyF_inputUnitA :    forall (V : obV log) (B : obA to) (A : obA from)
                                  (f : V(0 V |- to .-A[0 B ~> polyF0 dat A ]0 )0),
                                  f ~~ DesIdenObL (polyF  f A <o (from) .-uA)
        }.

    Existing Class extras.

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

    Global Arguments dataFun_of_dataFuntoCat : simpl never.

    Coercion extrasFun_of_extrasFuntoCat (dat : data) (ext : extras)  :  @FUNCTOR.extras log dat :=
      FUNCTOR.Extras (dat:=dat) (@CongPolyA _ _ from) (@polyA_arrow _ _ from) (@polyF_arrow dat ext)
                     (@polyF_morphism _ ext) (@CongPolyF _ ext) (@polyA_unitA _ _ from) (@polyA_inputUnitA _ _ from)
                     (@polyF_inputUnitA _ ext).

    Global Arguments extrasFun_of_extrasFuntoCat : simpl never.
    
    Structure functorToCat :=
      FunctorToCat {
          data_of :> data;
          extras_of :> @extras (data_of)
        }.

      (* is this necessary?*)
      Global Existing Instance extras_of.

      Coercion functor_of_functorToCat (func : functorToCat)
      : @FUNCTOR.functor log :=  {| FUNCTOR.data_of := data_of func; FUNCTOR.extras_of := extras_of func |}.
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

  End Context.
  Module Ex_Notations6.
    Notation "dat .-F|1" := (@polyF_unitB _ _ _ dat) (at level 0, format "dat .-F|1").
  End Ex_Notations6.
  Import Ex_Notations6.
  Notation "F|1" := (_ .-F|1) (at level 0).
  
  (*
     Variables (d : data) (e : @extras  d).
      Definition functor_fromto (*
                 (polyF0 : obA from -> obA to)
                 (polyF :   forall (V : obV log) (B : obA to) (A : obA from),
   V(0 V |- to .-A[0 B ~> polyF0 A ]0 )0 ->
   forall X : obA from,
     V(0 from .-A[0 A ~> X ]0 |- [0V ~> to .-A[0 B ~> polyF0 X ]0 ]0 )0)
                 (polyF_arrow :    forall (B : obA to) (A : obA from) (V V' : obV log) 
     (v : V(0 V' |- V )0) (f : V(0 V |- to .-A[0 B ~> polyF0 A ]0 )0)
     (X : obA from),
   polyF V' B A (f <o v) X ~~
         [1v ~> to .-A[0 B ~> polyF0 X ]0 ]0 <o polyF V B A f X )
                 (polyF_morphism :    forall (V : obV log) (B : obA to) (A : obA from) 
     (W : obV log) (A' : obA from) (g : V(0 W |- from .-A[0 A ~> A' ]0 )0)
     (f : V(0 V |- to .-A[0 B ~> polyF0 A ]0 )0) (X : obA from),
   polyF ((0W * V )0) B A'
     (Des
        ([1f ~> to .-A[0 B ~> polyF0 A' ]0 ]0 <o
         polyF (to .-A[0 B ~> polyF0 A ]0) B A 1 A' <o g)) X ~~
     DesIn ([0W ~> polyF V B A f X ]1 <o from .-A[1 g ~> X ]0) )
                 (CongPolyF :    forall (V : obV log) (B : obA to) (A : obA from)
     (f f' : V(0 V |- to .-A[0 B ~> polyF0 A ]0 )0),
                                   f' ~~ f -> forall X : obA from, polyF V B A f' X ~~ polyF V B A f X)
                 (polyF_inputUnitA :    forall (V : obV log) (B : obA to) (A : obA from)
     (f : V(0 V |- to .-A[0 B ~> polyF0 A ]0 )0),
                                          f ~~ DesIdenObL (polyF V B A f A <o (from) .-uA))
                 *)
      : @FUNCTOR.functor log.
        econstructor; cycle 1. Unshelve. Focus 2.
        econstructor.
        eexact (@polyA _ from).
        eexact (@polyA _ to).
        Unshelve. Focus 3.  eexact (@polyF0 d). Show Proof. exact (@polyF d). exact (@unitA _ from).
        
        econstructor;   cbn. Show Proof. exact (@CongPolyA _ _ from).
        Show Proof. exact (@polyA_arrow _ _ from).
        Show Proof. 
        exact (@polyF_arrow _ e).
        Show Proof.
        exact (@polyF_morphism _ e).
        Show Proof.
        exact (@CongPolyF _ e).
        exact (@polyA_unitA _ _ from).
        exact (@polyA_inputUnitA _ _ from).
        Show. exact (@polyF_inputUnitA _ e). Show Proof.
      Defined.
*)

(*
    Definition cst {T : Type} : T -> unit := fun x : T => tt.
    
    Section Context7.
      Context {log : logic}.
      
      Record data'' :=
        Data'' {
            obA_'' : Type;
            data1_of'' :> @data1 log obA_'' unit (@cst obA_'')
          }.
      
      Structure metafunctor :=
        Metafunctor {
            data_of'' :> data'';
            extras_of'' :> @extras _ _ _ _ (@data1_of'' data_of'')
          }.

    End Context7.
    *)



  (*TO REDO
        (*            Open Scope Ex_scope. *)
      Import Ex_Notations.
      Import Ex_Notations2.
Axiom      functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
      Definition catV (logV : logic ) (pf : @convV logV = fun V1 V2 => (eq : V(0 V1 |- V2 )0 -> V(0 V1 |- V2 )0 -> Prop) )
      (pf2: forall (V : obT) (B A : obV logV) (f f' : T(0 V |- V(0 B |- A )0 )0),
(forall _v : V,   f' _v ~~ f _v) ->
forall (X : obV logV) (a1 a2 : V(0 A |- X )0),
a1 ~~ a2 ->
(forall _v : V,  (V(1 f' |- X )0) a1 _v ~~ (V(1 f |- X )0) a2 _v) ->
 (V(1 f' |- X )0) = (V(1 f |- X )0)
 ) : @category logT.
      econstructor.
      Unshelve.
      Focus 2.
      econstructor.
      Unshelve. Focus 3. eapply (@obV logV).
      Focus 3. eapply (@polyV_relT00 logV).
      
      eapply (@polyV_relT logV).
      intros. intro. eapply (@IdenV logV). 

      econstructor;simpl. Show Proof. Show.

      simpl.    generalize (@Cong_polyV_relT (LOGIC.data_of logV) (LOGIC.extras_of logV)) .
      intros. simpl in H.  Check convV.   Eval unfold convV in H. Check H.  erewrite  !pf in *.
      Check  V(1 f' |- X )0.  eapply pf2. rewrite H0. reflexivity. reflexivity.
      apply H. rewrite H0. reflexivity. reflexivity.

      simpl.  generalize (@polyV_relT_arrow (LOGIC.data_of logV) (LOGIC.extras_of logV)) .
      intros.  erewrite  !pf in *.
      simpl. unfold polyT_relT. unfold consT10. simpl.
      apply functional_extensionality_dep. intro.
      apply functional_extensionality_dep. intro. apply H.
Show Proof.
      simpl.  generalize (@polyV_relT_morphism (LOGIC.data_of logV) (LOGIC.extras_of logV)) .
      intros.  erewrite  !pf in *.
      simpl. unfold polyT_relT. unfold consT10, consT01. 
      apply functional_extensionality_dep. intro.
      apply functional_extensionality_dep. intro. simpl. unfold DesT. simpl.  unfold DesIn.  unfold Cons. unfold Des. simpl.
      unfold DesT. simpl. unfold ConsT. simpl. unfold polyT_relT. simpl.   unfold polyV_relT_unitary in *. unfold polyV_relT_identitary in *.   simpl in *.  eapply   H. erewrite <- H. 

      simpl.
      eapply H in pf2. About Cong_polyV_relT. unfold polyV_relT. 
      shelve.
      simpl.
      shelve.
      simpl. Show Proof. Print extras. intros. intro.  Check polyV_relT_arrow. Show Proof. eapply (@polyV_relT_arrow (LOGIC.data_of logV) (LOGIC.extras_of logV) ). .  intro.  eapply (@polyV_relT_arrow logV).
      *)

  Export FUNCTOR.
End FUNCTORTOCAT.
                                                                                                                                                                                    

Module TRANSFORMATION.
  Import FUNCTORTOCAT.
  Import Ex_Notations4.
  Set Implicit Arguments.
  Unset Strict Implicit.

  Section Context.
    Context {log : logic} {catA : category log} {catB : category log}.
    Variable (funF : functorToCat catA catB).
    Variable (funG : functorToCat catA catB).

    Record data :=
      Data {
          polyβ : forall (V : obV log) (B : obA catB) (A : obA catA),
                        V(0 V |- funF.-F[0 B ~> A ]0 )0 ->
                        V(0 V |- funG.-F[0 B ~> A ]0 )0
        }.

  End Context.

  Module Ex_Notations5.
    Notation "dat .-β|1 f" := (@polyβ _ _ _ _ _ dat _ _ _ f) (at level 5, right associativity, format "dat .-β|1  f").
    Notation "dat .-β|0 A" := (@polyβ _ _ _ _ _ dat _ _ A (@IdenV _)) (at level 4, right associativity, format "dat .-β|0  A").
  End Ex_Notations5.

  Import Ex_Notations5.
  Notation "β|1 f" := (_.-β|1 f) (at level 5, right associativity).
  Notation "β|0 A" := (_.-β|0 A) (at level 4, right associativity).

  Section Context2.
    Context {log : logic} {catA : category log} {catB : category log}.
    Variable (funF : functorToCat catA catB).
    Variable (funG : functorToCat catA catB).
  

    Record extras {dat : data funF funG} :=
      Extras {
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

    Existing Class extras.

    Structure transformation :=
      Transf {
          data_of :> data funF funG;
          extras_of :> @extras (data_of)
        }.

    (* is this necessary?*)
    Global Existing Instance extras_of.

  End Context2.
End TRANSFORMATION.

Module FUNCOMP.
  Import FUNCTORTOCAT.
  Import Ex_Notations4.
  Set Implicit Arguments.
  Unset Strict Implicit.

  Section Context.
    Context {log : logic} {catA : category log} {catB : category log} {catC : category log}.
    Variable (funF : functorToCat catA catB).
    Variable (funF' : functorToCat catB catC).

    Definition composition_F'_after_F :
      forall (V : obV log) (B : obA catB) (A : obA catA),
      forall (b : V(0 V |- catB.-A[0 B ~> funF.-F|0 A ]0 )0),
      forall (W : obV log) (C : obA catC),
      forall (c : V(0 W |- catC.-A[0 C ~> funF'.-F|0 B]0 )0),
      forall X : obA catA, V(0 A[0 A ~> X ]0  |- [0 V ~> [0 W ~> catC.-A[0 C ~> funF'.-F|0 funF.-F|0 X ]0 ]0 ]0 )0.
    Proof.
      intros.
      eapply @polyV_relT_identitary (* _ <o _ *). apply consV01.
      eapply (@FUNCTOR.polyF log funF' _ _ _ c).
      eapply (@FUNCTOR.polyF log funF _ _ _ b).
    Defined.

    Definition composition_F'_after_F_simple :
      forall  (A : obA catA),
      forall (W : obV log) (C : obA catC),
      forall (c : V(0 W |- catC.-A[0 C ~> funF'.-F|0 funF.-F|0 A ]0 )0),
      forall X : obA catA, V(0 A[0 A ~> X ]0  |- [0 W ~> catC.-A[0 C ~> funF'.-F|0 funF.-F|0 X ]0 ]0 )0.
    Proof.
      intros.
      apply DesIdenObR.
      eapply composition_F'_after_F.
      eapply (@unitA _ catB).
      exact c.
    Defined.

     Unset Printing Implicit Defensive.
     Definition data_of_funComp : FUNCTORTOCAT.data catA catC :=
       {|
         FUNCTORTOCAT.polyF0 := fun A  => funF'.-F|0 funF.-F|0 A;
         FUNCTORTOCAT.polyF := fun V C A c X =>  composition_F'_after_F_simple c X |}.
     (* econstructor.
     Unshelve. 2: intro A; exact (funF'.-F|0 funF.-F|0 A).
     intros; eapply composition_F'_after_F_simple. assumption.
     *)
     Definition extras_of_funComp : @FUNCTORTOCAT.extras _ _ _ data_of_funComp.
       Admitted.

     Definition funComp : functorToCat catA catC :=
       {|
         FUNCTORTOCAT.data_of := data_of_funComp;
         FUNCTORTOCAT.extras_of := extras_of_funComp |}.

     Lemma composition_F'_after_F_identitary_polyF'_identitary_polyF_unitary :    forall (C : obA catC) (A X : obA catA),
                                                                                    (funF'.-F[0 C ~> - ]1) funF.-F|0 A funF.-F|0 X <o F|1 A X ~~ (funComp.-F[0 C ~> - ]1) A X.
     Proof.
       intros. apply SymV, DesIdenObR_output.
     Qed.
  End Context.
End FUNCOMP.


    (*            >>>---   NEXT IS WHY : ALL THIS WORK OF INTERFACING FOR INSTANCES WAS DONE  ---<<<   

apply this to unfold this as identitary (external-structural) of composition of polyfunctors ( polyV_relV o (poly_of_meta F[0 B ~> - ]1) ) .. ( polyV_relV o (poly_of_meta metaFB) )  ...  show before that
1. NEXT1 some metafunctor metaFB into catV on top of F[0 B ~> - ]1  by polyF which becomes  metaFB := meta_of_poly F at B,
2. then get derived polyfunctor from this metafunctor, 
3. then unitary( |1 ) of this derived polyfunctor is  identitary( ||1 ) of the metafunctor metaFB on top of F[0 B ~> - ]1 
4. NEXT2 which is  identitary ( [B ~> - ]1 ) of original polyfunctor F
 
all: ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 A' X   
       ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o (meta_of_poly F at B)||1 A' X    
       ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o FB||1 A' X    
       ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o (poly_of_meta metaFB)|1 A' X
       (polyV_relV o (poly_of_meta metaFB))[0 V ~> - ]1 A' X
       (meta_of_poly (polyV_relV o (poly_of_meta (meta_of_poly F at B))) at V)||1 A' X

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
      ... == natural_metatransformation from (meta_of_poly polyA at A) to (meta_of_poly (polyV_relV o (poly_of_meta (meta_of_poly F at B))) at V) by β at A' at X

NEXT3: naturality of any metatransformation of any metafunctors <-> polymorphism of coresp polytransformation of coresp polyfuntors
NEXT4: rewrite natural as above

     *)




     


(** SOURCE SCRATCH DRAFT BELOW **)
      
(** ** put functional monoidal logic onto V **)

Variable desV00 : forall V2 : obV, forall V1 : obV, obV.
Notation  "(0 V1 * V2 )0" := (desV00 V2 V1) (at level 30, V1 at next level).
Check ( fun V2 V1 => (0 V1 *  V2 )0  ).
Variable desV10 : forall V2 : obV, forall V1 V1' (v : V(0 V1 |- V1' )0),  V(0 (0 V1* V2 )0 |- (0 V1' * V2 )0 )0.
Notation  "(1 v * V2 )0" := (desV10 V2 v) (at level 30, v at next level).
Check ( fun V2 v => (1 v *  V2 )0  ).

Variable consV00 : obV -> obV -> obV.
Notation "[0 V1 ~> V2 ]0" := (consV00 V1 V2) (at level 30).
Variable consV01 : forall V1 : obV, forall V2 V2' (v : V(0 V2 |- V2' )0), V(0 [0 V1 ~> V2 ]0 |- [0 V1 ~> V2' ]0 )0.
Notation "[0 V1 ~> v ]1" := (consV01 V1 v) (at level 30).
Variable consV10 : forall V1' V1 (v : V(0 V1' |- V1)0), forall V2 : obV, V(0 [0 V1 ~> V2 ]0 |- [0 V1' ~> V2 ]0 )0.
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
Notation "F[0 B ~> A ]0" := (polyF00 B A) (at level 25).

Parameter polyF : forall (B : obF), forall (V : obV) (A : obF),
                    V(0 V |- F[0 B ~> A ]0 )0 ->
                    forall X : obF, V(0 F[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0.

(** therefore "F[1 b ~> X ]0" is similar to ( b o> _ ) **)
Notation "F[1 b ~> X ]0" := (@polyF _ _ _ b X) (at level 25).

(** therefore "F[0 X ~> a ]1" is similar to the common ( _ o> a ) ,   more precisely ( (id _) o> a )   **)
Notation "F[0 X ~> a ]1" := (@polyF _ _ _ (@IdenV _) X <o (a : V(0 _ |- F[0 _ ~> X ]0 )0)) (at level 25).
(** memo: may attempt  "F[1 b ~> a ]1" ,  shall be similar to the common ( (b _i) o> a ) 
therefore "F[1 _1 ~> _2 ]1 _3 shall be ( (_1 _3) o> _2 ) **)

(** related to correspondence with the common representation **)
Variable polyF_arrow :  forall (B : obF), forall (A : obF),
                        forall (V V' : obV) (v : V(0 V' |- V )0),
                        forall (f : V(0 V |- F[0 B ~> A ]0 )0) (X : obF),
                          F[1 f <o v ~> X ]0
                           ~~ [1 v ~> F[0 B ~> X ]0 ]0 <o F[1 f ~> X ]0 .

(** related to associativity, polyF_morphism says that, put the parameter f and the modifier argument g, then get
xxERASE        (outer modification)    ( g <o f ) o> _  =  f o> ( g o> _ )    (inner modification)
           (outer modification)    ( (f ) o> g ) o> _  =  f o> ( g o> _ )    (inner modification)
which is, holding only f as parameter and running all the arguments,
xxERASE        (outer modification)    ( _1 <o f ) o> _2  =  f o> ( _1 o> _2 )    (inner modification)
           (outer modification)    ( (f ) o> _1 ) o> _2  =  f o> ( _1 o> _2 )    (inner modification)
 **)
(** written here :   (outer modification) ~~ (inner modification) **)
Variable polyF_morphism :  forall (B : obF), forall (V : obV),
                           forall (A : obF) (W : obV) (A' : obF) (g : V(0 W |- F[0 A ~> A']0 )0),
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

Variable polyV_relV : forall (W : obV), forall (U : obV) (V : obV),
                   V(0 U |- [0 W ~> V ]0 )0 ->
                   forall X : obV, V(0 [0 V ~> X ]0  |- [0 U ~> [0 W ~> X ]0 ]0 )0.

Notation "V[0 U ~> V ]0" := ([0 U ~> V ]0) (at level 25, only parsing).
Notation "V[1 v ~> X ]0" := (@polyV_relV _ _ _ v X) (at level 25).
Notation "V[0 X ~> w ]1" := (@polyV_relV _ _ _ 1 X <o w) (at level 25).
Notation "V[0 W ~> - ]1" := (fun V X => @polyV_relV _ _ _ (@IdenV ([0 W ~> V ]0)) X) (at level 25). 

Hypothesis polyV_relV_polyV_relT : forall (W : obV), forall (U : obV) (V : obV),
                         forall (v : V(0 U |- [0 W ~> V ]0 )0), forall X : obV,
                           [1 Des v ~> X]0
                                         ~~ DesIn( V[1 v ~> X ]0 ) .

Hypothesis polyV_relV_arrow :  forall (B : obV) (A : obV) (V : obV),
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
  eapply CongCom; [ | eapply ReflV]; apply polyV_relV_polyV_relT.
Qed.

(** polyF_natural (sym) says that, put the parameter f, then get
xxERASE        (outer modification)    _1 <o ( f o> _2 )  =  f o> ( _1 <o _2 )    (inner modification)
           (outer modification)    ( f o> _2 ) o> _1  =  f o> ( _2 o> _1 )    (inner modification)
and this is codeductible with polyF_morphism above which says that, put the parameter f, then get
xxERASE       (outer modification)    ( _1 <o f ) o> _2  =  f o> ( _1 o> _2 )    (inner modification)
          (outer modification)    ( (f ) o> _1 ) o> _2  =  f o> ( _1 o> _2 )    (inner modification)
xxERASE now memo that in the left hand sides there is mirroring of whole and permutation of inputs, and that in the right hand sides there is mirroring of block and permutation of inputs,
xxnow memo that in the left hand sides there is permutation of inputs, and that in the right hand sides there is mirroring of block and permutation of inputs,
now memo that in the left hand sides there is permutation of inputs, and that in the right hand sides there is permutation of inputs,  **)
(** written here :   (inner modification) ~~ (outer modification) **)
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

  (* convert right hand side : outer polyV_relV_arrow then outer polyF_arrowIn which is inner form of polyF_arrow *)
  assert ( RHS1 : DesIn( ( V[1 (@IdenV (V[0 V ~> (F[0 B ~> C ]0) ]0)) <o (F[1 f ~> C ]0) ~> (F[0 B ~> X ]0) ]0 ) <o F[0 B ~> - ]1 C X )
                       ~~ DesIn( [1 F[1 f ~> C ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0 <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) )
    by ( eapply TransV; [ eapply CongDesIn; eapply Cat2V | ];
         apply CongDesIn; apply CongCom; [ | apply ReflV];
         apply polyV_relV_arrow ).

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

Hypothesis consV10_functorial : forall V1' V1 (v :  V(0 V1' |- V1 )0), forall V1'' (v' : V(0 V1'' |- V1' )0), forall V2 : obV,
                                  [1 v <o v' ~> V2 ]0 ~~  [1 v' ~> V2 ]0 <o  [1 v ~> V2 ]0 .
Hypothesis consV11_bifunctorial : forall V1' V1 (v : V(0 V1' |- V1 )0), forall W1 W1' (w : V(0 W1 |- W1' )0),
                                    [0 V1' ~> w ]1 <o  [1 v ~> W1 ]0 ~~ [1 v ~> W1' ]0 <o [0 V1 ~> w ]1 .
Hypothesis CongConsV10 : forall V1' V1 (v v' : V(0 V1' |- V1)0), forall V2 : obV,
                           v' ~~ v -> [1 v' ~> V2 ]0 ~~ [1 v ~> V2 ]0 .

(** related to non-variance when unit pull the input, commonly  ( 1 o> h ) ~~ h  **)
Hypothesis polyF_unitF : forall (A : obF), forall X : obF, (@IdenV (F[0 A ~> X ]0)) ~~ DesIdenObR( F[1 (@unitF A) ~> X ]0 ) .

(** related to non-variance when unit push the output, commonly  ( (f _i) o> 1 ) ~~ (f _i)  , 
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


(** ** polymorph functor **)

Module Functor.
  
  (** short : instead of describing F : catA --> catB  then (contrast yoneda structures) describe catV[ V , catB[ B , F - ] ] : catA --> catV **)

  (** ** put some polymorph category A , note that unitA is lacked later**)

  Variable obA : Type.
  Variable polyA00 : obA -> obA -> obV.
  Notation "A[0 A1 ~> A2 ]0" := (polyA00 A1 A2) (at level 25).

  Parameter polyA : forall (A2 : obA), forall (V : obV) (A1 : obA),
                      V(0 V |- A[0 A2 ~> A1 ]0 )0 ->
                      forall X : obA, V(0 A[0 A1 ~> X ]0  |- [0 V ~> A[0 A2 ~> X ]0 ]0 )0.

  (** therefore "A[1 f ~> X ]0" is similar to ( f o> _ ) **)
  Notation "A[1 f ~> X ]0" := (@polyA _ _ _ f X) (at level 25).

  (** therefore "A[0 X ~> g ]1" is similar to the common ( _ <o g ) **)
  Notation "A[0 X ~> g ]1" := (@polyA _ _ _ (@IdenV _) X <o (g : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).

  Definition polyA_IdenV : forall (B : obA), forall (A : obA),
                           forall X : obA, V(0 A[0 A ~> X ]0  |- [0 A[0 B ~> A ]0 ~> A[0 B ~> X ]0 ]0 )0
    := (fun B A X => @polyA B (A[0 B ~> A ]0) A (@IdenV (A[0 B ~> A ]0)) X).
  Notation "A[0 B ~> - ]1" := (@polyA_IdenV B) (at level 25).

  (** ** put some polymorph category B , note that unitB is not lacked  **)

  Variable obB : Type.
  Variable polyB00 : obB -> obB -> obV.
  Notation "B[0 B1 ~> B2 ]0" := (polyB00 B1 B2) (at level 25).

  Parameter polyB : forall (B2 : obB), forall (V : obV) (B1 : obB),
                      V(0 V |- B[0 B2 ~> B1 ]0 )0 ->
                      forall Y : obB, V(0 B[0 B1 ~> Y ]0  |- [0 V ~> B[0 B2 ~> Y ]0 ]0 )0.

  (** therefore "B[1 m ~> Y ]0" is similar to ( m o> _ ) **)
  Notation "B[1 m ~> Y ]0" := (@polyB _ _ _ m Y) (at level 25).

  (** therefore "B[0 Y ~> n ]1" is similar to the common ( _ <o n ) **)
  Notation "B[0 Y ~> n ]1" := (@polyB _ _ _ (@IdenV _) Y <o (n : V(0 _ |- B[0 _ ~> Y ]0 )0)) (at level 25).

  Definition polyB_IdenV : forall (B : obB), forall (A : obB),
                           forall X : obB, V(0 B[0 A ~> X ]0  |- [0 B[0 B ~> A ]0 ~> B[0 B ~> X ]0 ]0 )0
    := (fun B A X => @polyB B (B[0 B ~> A ]0) A (@IdenV (B[0 B ~> A ]0)) X).
  Notation "B[0 B ~> - ]1" := (@polyB_IdenV B) (at level 25).

  (** ** get some polymorph funtor F **)

  Variable polyF0 : obA -> obB.
  Notation "F|0 A" := (polyF0 A) (at level 4, right associativity).

  (* want B[ B , F A1] -> forall A2, A[ A1 , A2] -> B[ B , F A2 ] *)
  (*       (F|1 _2 ) <o _1   ...   _1 o> (F|1 _2)      *)

  Parameter polyF : forall (V : obV) (B : obB) (A : obA),
                      V(0 V |- B[0 B ~> F|0 A ]0 )0 ->
                      forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> B[0 B ~> F|0 X ]0 ]0 )0.

  (** :^) **)
  Notation "F[0 B ~> A ]0" := (B[0 B ~> F|0 A ]0) (at level 25).
  
  (** therefore "F[1 b ~> X ]0" is similar to   ( b o> ( F|1 _ ) )   , alternatively   ( b o>F _ )   **)
  Notation "F[1 b ~> X ]0" := (@polyF _ _ _ b X) (at level 25).

  (** therefore "F[0 X ~> a ]1" is similar to   ( B[0 B ~> ( F|1 a ) ]1 ) which is ( _ o> ( F|1 a ) )   , alternatively  ( _ o>F a )   **)
  Notation "F[0 X ~> a ]1" := (@polyF _ _ _ (@IdenV _) X <o (a : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).

  (** NOT LACKED, may attempt
  (* for now, unitB for this notation only *)
  Parameter unitB : forall {B : obB}, V(0 I |- B[0 B ~> B ]0 )0.
  Notation "'uB'" := (@unitB _) (at level 0).
  (* approximative notation, may require input (g : V(0 I |- A[0 A ~> X ]0 )0) but not really more progress,
      and may transform output to cancel ( [0 I ~>  _ ]0 ) and now more progress *)
  Notation "F|1 a" := (DesIdenObR ([1 uB ~> _ ]0 <o F[0 _ ~> a ]1)) (at level 5, right associativity) .
  Check (fun (W : obV) (A X : obA) (a : V(0 W |- A[0 A ~> X ]0 )0) => F|1 a).
   **)
  
  (** related to correspondence with the common representation **)
  Variable polyF_arrow : forall (B : obB) (A : obA),
                         forall (V V' : obV) (v : V(0 V' |- V )0),
                         forall (f : V(0 V |- F[0 B ~> A ]0 )0) (X : obA),
                           F[1 f <o v ~> X ]0
                            ~~ [1 v ~> F[0 B ~> X ]0 ]0 <o F[1 f ~> X ]0 .

  (** related to associativity, polyF_morphism says that, put the parameter f and the modifier argument g, then get
           (outer modification)    ( (f ) o>F g ) o>F _  =  f o>F ( g o> _ )    (inner modification)
which is, holding only f as parameter and running all the arguments,
           (outer modification)    ( (f ) o>F _1 ) o>F _2  =  f o>F ( _1 o> _2 )    (inner modification)
   **)
  (** written here :   (outer modification) ~~ (inner modification) **)
  Variable polyF_morphism : forall (V : obV) (B : obB),
                            forall (A : obA) (W : obV) (A' : obA) (g : V(0 W |- A[0 A ~> A']0 )0),
                            forall (f : V(0 V |-F[0 B ~> A ]0 )0) (X : obA),
                              F[1 Des( [1 f ~> F[0 B ~> A' ]0 ]0 <o F[0 A' ~> g ]1 ) ~> X]0
                               ~~  DesIn( [0 W ~> F[1 f ~> X ]0 ]1 <o A[1 g ~> X ]0 ).

  Definition polyF_IdenV : forall (B : obB) (A : obA),
                           forall X : obA, V(0 A[0 A ~> X ]0  |- [0 F[0 B ~> A ]0 ~> F[0 B ~> X ]0 ]0 )0
    := (fun B A X => @polyF (F[0 B ~> A ]0) B A (@IdenV (F[0 B ~> A ]0)) X).
  Notation "F[0 B ~> - ]1" := (@polyF_IdenV B) (at level 25).

  Hypothesis CongPolyF : forall (V : obV) (B : obB) (A : obA),
                         forall (f f' : V(0 V |- F[0 B ~> A ]0 )0),
                           f' ~~ f -> forall X : obA, polyF f' X ~~ polyF f X.

  (** ** get that the image of polyF are contained in natural transformations **)

  (** for polymorph functor, get this copy-paste same deduction as for polymorph category **)
  Lemma polyF_arrowIn : forall (B : obB) (A : obA),
                        forall (V W V' : obV) (v : V(0 W |- [0 V' ~> V ]0 )0),
                        forall (f : V(0 V |- F[0 B ~> A ]0 )0) (X : obA),
                          F[1 f <o (Des v) ~> X ]0
                           ~~ DesIn( V[1 v ~> F[0 B ~> X ]0 ]0 <o F[1 f ~> X ]0 ) .
  Proof.
    intros; eapply TransV; [ apply DesIn_Input | ].
    eapply TransV; [ | apply polyF_arrow ].
    eapply CongCom; [ | eapply ReflV]; apply polyV_relV_polyV_relT.
  Qed.

  (** polyF_natural (sym) says that, put the parameter f, then get
           (outer modification)    ( f o>F _2 ) o>F _1  =  f o>F ( _2 o> _1 )    (inner modification)
and this is codeductible with polyF_morphism above which says that, put the parameter f, then get
           (outer modification)    ( (f ) o>F _1 ) o>F _2  =  f o>F ( _1 o> _2 )    (inner modification)
now memo that in the left hand sides there is permutation of inputs, and that in the right hand sides there is permutation of inputs,  **)
  (** written here :   (inner modification) ~~ (outer modification) **)
  (** for polymorph functor, get this copy-paste same deduction as for polymorph category **)
  Lemma polyF_natural : forall (V : obV) (B : obB) (A : obA) (f : V(0 V |- F[0 B ~> A ]0)0),
                        forall (C X : obA),
                          ( [0 A[0 A ~> C ]0 ~> F[1 f ~> X ]0 ]1
                            <o A[0 A ~> - ]1 C X )
                            ~~ ( [1 F[1 f ~> C ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
                                 <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) .
  Proof.
    (* enough ( DesIn( _ ) ~~ DesIn( _ ) ) *)
    intros;  eapply TransV; [ eapply TransV | ]; [ apply ConsIn_DesIn | idtac | apply SymV, ConsIn_DesIn].
    apply CongConsIn.

    (* convert left hand side : outer polyF_morphism then inner polyF_arrow *)
    assert ( LHS1 : F[1 Des( [1 f ~> F[0 B ~> C ]0 ]0 <o F[0 C ~> (@IdenV (A[0 A ~> C]0)) ]1 ) ~> X ]0
                     ~~ DesIn( [0 A[0 A ~> C ]0 ~> F[1 f ~> X ]0 ]1 <o A[0 A ~> - ]1 C X ) )
      by apply polyF_morphism.

    assert ( LHS2 : F[1 Des( F[1 (@IdenV (F[0 B ~> A ]0)) <o f ~> C ]0 ) ~> X ]0
                     ~~ F[1 Des( [1 f ~> F[0 B ~> C ]0 ]0 <o F[0 C ~> (@IdenV (A[0 A ~> C ]0)) ]1 ) ~> X ]0 )
      by ( apply CongPolyF, CongDes;  eapply TransV; [ eapply Cat2V | ]; eapply TransV; [ eapply Cat1RightV | ];
           apply polyF_arrow ).

    (* convert right hand side : outer polyV_relV_arrow then outer polyF_arrowIn which is inner form of polyF_arrow *)
    assert ( RHS1 : DesIn( ( V[1 (@IdenV (V[0 V ~> (F[0 B ~> C ]0) ]0)) <o (F[1 f ~> C ]0) ~> (F[0 B ~> X ]0) ]0 ) <o F[0 B ~> - ]1 C X )
                         ~~ DesIn( [1 F[1 f ~> C ]0 ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0 <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) )
      by ( eapply TransV; [ eapply CongDesIn; eapply Cat2V | ];
           apply CongDesIn; apply CongCom; [ | apply ReflV];
           apply polyV_relV_arrow ).

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

  Definition natural (V : obV) (B : obB) (A : obA) (β : forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0) :=
    forall (C X : obA),
      ( [0 A[0 A ~> C ]0 ~> β X ]1
        <o A[0 A ~> - ]1 C X )
        ~~ ( [1 β C ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
             <o ( V[0 V ~> - ]1 (F[0 B ~> C ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 C X ) .

  Lemma polyF_natural_folded : forall (V : obV) (B : obB) (A : obA) (b : V(0 V |- F[0 B ~> A ]0)0),
                                 natural (fun X : obA => F[1 b ~> X ]0).
  Proof.
    unfold natural.
    exact polyF_natural.
  Qed.

  (** ** get that the image of polyF contains all natural transformations **)

  Hypothesis CongPolyA : forall (B : obA), forall (V : obV) (A : obA),
                         forall (f f' : V(0 V |- A[0 B ~> A ]0 )0),
                           f' ~~ f -> forall X : obA, polyA f' X ~~ polyA f X.

  Variable polyA_arrow :  forall (B : obA), forall (A : obA),
                          forall (V V' : obV) (v : V(0 V' |- V )0),
                          forall (f : V(0 V |- A[0 B ~> A ]0 )0) (X : obA),
                            A[1 f <o v ~> X ]0
                             ~~ [1 v ~> A[0 B ~> X ]0 ]0 <o A[1 f ~> X ]0 .

  Parameter unitA : forall {A : obA}, V(0 I |- A[0 A ~> A ]0 )0.
  Notation "'uA'" := (@unitA _) (at level 0).

  Hypothesis polyA_unitA : forall (A : obA), forall X : obA, (@IdenV (A[0 A ~> X ]0)) ~~ DesIdenObR( A[1 (@unitA A) ~> X ]0 ) .

  Hypothesis polyA_inputUnitA : forall (B : obA), forall (V : obV) (A : obA),
                                forall (f : V(0 V |- A[0 B ~> A ]0 )0),
                                  f  ~~ DesIdenObL( (A[1 f ~> A ]0) <o (@unitA A) ).

  (** for polymorph functor, get this copy-paste same deduction as for polymorph category **)
  Lemma natural_unitF_explicit : forall (V : obV) (B : obB) (A : obA) (φ : forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0),
                                   natural φ ->
                                   forall (X : obA),
                                     DesIdenObR( [1 φ A <o (@unitA A) ~> [0 V ~> F[0 B ~> X ]0 ]0 ]0
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
  Lemma natural_unitF : forall (V : obV) (B : obB) (A : obA) (φ φ' : forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0),
                          natural φ -> natural φ' ->
                          φ' A <o (@unitA A)  ~~ φ A <o (@unitA A) ->
                          forall X : obA, φ' X ~~ φ X.
  Proof.
    intros; eapply TransV; [ apply natural_unitF_explicit; assumption |
                             eapply TransV; [ | apply SymV, natural_unitF_explicit; assumption ] ].
    apply CongDesIdenObR, CongCom; [ | apply ReflV ]; apply CongConsV10.
    assumption.
  Qed.

  (** related to non-variance when unit push the output, commonly  ( (f _i) o>F 1 ) ~~ (f _i)  , 
       therefore polyF is injective **)
  Hypothesis polyF_inputUnitA : forall (V : obV) (B : obB) (A : obA),
                                forall (f : V(0 V |- F[0 B ~> A ]0 )0),
                                  f ~~ DesIdenObL( (F[1 f ~> A ]0) <o (@unitA A) ).

  (** for polymorph functor, get this copy-paste same deduction as for polymorph category **)
  Lemma YONEDA : forall (V : obV) (B : obB) (A : obA) (φ φ' : forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> F[0 B ~> X ]0 ]0 )0),
                   natural φ ->
                   forall X : obA, φ X ~~ F[1 DesIdenObL( (φ A) <o (@unitA A) ) ~> X ]0 .
  Proof.
    intros; enough( φ A <o (@unitA A) ~~ F[1 DesIdenObL( (φ A) <o (@unitA A) ) ~> A ]0 <o (@unitA A) ).
    apply natural_unitF; [ |  assumption | assumption ] .
    unfold natural; intros; apply polyF_natural.
    
    eapply TransV; [ apply SymV, ConsIdenObL_DesIdenObL | ].
    eapply TransV; [ | apply ConsIdenObL_DesIdenObL].
    apply CongConsIdenObL.
    eapply TransV; [ apply polyF_inputUnitA |  apply ReflV ].
  Qed.


  (** ** polymorph polytransformation **)

  Module Transformation.

    (** short : instead of describing φ A : G A -> H A  then a-la-dosen (contrast weighted colimiting Kan extension) describe φ _f : catV( V , catB[ B , G A ] ) ->  catV( V , catB[ B , H A ] ) **)

    (** ** put some polymorph funtor G **)

    Variable polyG0 : obA -> obB.
    Notation "G|0 A" := (polyG0 A) (at level 4, right associativity).

    Parameter polyG : forall (V : obV) (B : obB) (A : obA),
                        V(0 V |- B[0 B ~> G|0 A ]0 )0 ->
                        forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> B[0 B ~> G|0 X ]0 ]0 )0.

    Notation "G[0 B ~> A ]0" := (B[0 B ~> G|0 A ]0) (at level 25).
    Notation "G[1 b ~> X ]0" := (@polyG _ _ _ b X) (at level 25).
    Notation "G[0 X ~> a ]1" := (@polyG _ _ _ (@IdenV _) X <o (a : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).

    Variable polyG_arrow : forall (B : obB) (A : obA),
                           forall (V V' : obV) (v : V(0 V' |- V )0),
                           forall (f : V(0 V |- G[0 B ~> A ]0 )0) (X : obA),
                             G[1 f <o v ~> X ]0
                              ~~ [1 v ~> G[0 B ~> X ]0 ]0 <o G[1 f ~> X ]0 .

    Variable polyG_morphism : forall (B : obB) (V : obV),
                              forall (A : obA) (W : obV) (A' : obA) (g : V(0 W |- A[0 A ~> A']0 )0),
                              forall (f : V(0 V |-G[0 B ~> A ]0 )0) (X : obA),
                                G[1 Des( [1 f ~> G[0 B ~> A' ]0 ]0 <o G[0 A' ~> g ]1 ) ~> X]0
                                 ~~  DesIn( [0 W ~> G[1 f ~> X ]0 ]1 <o A[1 g ~> X ]0 ).

    Definition polyG_IdenV : forall (B : obB) (A : obA),
                             forall X : obA, V(0 A[0 A ~> X ]0  |- [0 G[0 B ~> A ]0 ~> G[0 B ~> X ]0 ]0 )0
      := (fun B A X => @polyG (G[0 B ~> A ]0) B A (@IdenV (G[0 B ~> A ]0)) X).
    Notation "G[0 B ~> - ]1" := (@polyG_IdenV B) (at level 25).

    Hypothesis CongPolyG : forall (V : obV) (B : obB) (A : obA),
                           forall (f f' : V(0 V |- G[0 B ~> A ]0 )0),
                             f' ~~ f -> forall X : obA, polyG f' X ~~ polyG f X.
    
    (** ** get some polymorph polytransformation β **)
    
    Parameter polyβ : forall (V : obV) (B : obB) (A : obA),
                        V(0 V |- F[0 B ~> A ]0 )0 ->
                        V(0 V |- G[0 B ~> A ]0 )0 .

    (** :^) **)
    Notation "β|1 f" := (@polyβ _ _ _ f) (at level 5, right associativity).
    Notation "β|0 A" := (@polyβ _ _ A (@IdenV _)) (at level 4, right associativity).

    Variable polyβ_arrow : forall (B : obB) (A : obA),
                           forall (V V' : obV) (v : V(0 V' |- V )0),
                           forall (f : V(0 V |- F[0 B ~> A ]0 )0),
                             β|1 (f <o v)
                                 ~~ β|1 f <o v .

    (** written here : (inner modification) ~~ (outer modification)**)
    Variable polyβ_morphism : forall (V : obV) (B : obB),
                              forall (A : obA) (W : obV) (A' : obA) (a : V(0 W |- A[0 A ~> A']0 )0),
                              forall (f : V(0 V |- F[0 B ~> A ]0 )0),
                                β|1 (Des( [1 f ~> F[0 B ~> A' ]0 ]0 <o F[0 A' ~> a ]1 ))
                                    ~~ (Des( [1 β|1 f ~> G[0 B ~> A' ]0 ]0 <o G[0 A' ~> a ]1 )) .

    Variable polyβ_morphism_codomain : forall (V : obV),
                                       forall (B : obB) (W : obV) (B' : obB) (b : V(0 W |- B[0 B' ~> B]0 )0),
                                       forall (A : obA),
                                       forall (f : V(0 V |-F[0 B ~> A ]0 )0),
                                         β|1 (Des( B[1 b ~> F|0 A ]0 <o f ))
                                             ~~  Des( B[1 b ~> G|0 A ]0 <o β|1 f ).

    (** next :
     1. define naturality of any transformation of polymorph functors into catV
     2. show codeductibility of naturality for this transformation in catV with polymorphism (polymorph in V , B is easy) for the corresponding polytransformation
     3. define composition of polymorph functors, view [0 V0 ~> F[0 B0 ~> - ]0 ]0 as coming from composite polymorph functors
     4. confirm old naturality signify new naturality of the transformation F[1 (f0 : V(0 V0 |- F[0 B0 ~> A0 ]0 )0) ~> - ]0 between these polymorph functors on top of A[0 A0 ~> - ]0 (which is polyA) and on top of [0 V0 ~> F[0 B0 ~> - ]0 ]0 (which is composite of polyV_relV with polyF)
     5. rewrite the yoneda lemma as saying that the image is precisely any transformation whose corresponding polytransformation is polymorph
     **)

    (** alternatively, more immediately and particularly, show that poly_of_this_transf below satisfies polyβ_arrow (easy) and polyβ_morphism_codomain (easy) and polyβ_morphism (from old naturality) **)
    Definition poly_of_this_transf : forall (A0 : obA) (V0 : obV) (B0 : obB) (f0 : V(0 V0 |- F[0 B0 ~> A0 ]0 )0),
                                     forall (V : obV) (U : obV) (A : obA),
                                       V(0 V |- V[0 U ~> A[0 A0 ~> A ]0 ]0 )0 ->
                                       V(0 V |- V[0 U ~> [0 V0 ~> F[0 B0 ~> A ]0 ]0 ]0 )0
      := fun (A0 : obA) (V0 : obV) (B0 : obB) (f0 : V(0 V0 |- F[0 B0 ~> A0 ]0 )0)
         => fun (V : obV) (U : obV) (A : obA)
           => fun (f : V(0 V |- V[0 U ~> A[0 A0 ~> A ]0 ]0 )0)
             => [0 U ~> F[1 f0 ~> A ]0 ]1 <o f .


    Section FunctorComposition.

      (** ** composition of two polyfunctors, 
                  now put some polymorph category C , note that unitB is lacked  **)

      Variable obC : Type.
      Variable polyC00 : obC -> obC -> obV.
      Notation "C[0 C1 ~> C2 ]0" := (polyC00 C1 C2) (at level 25).

      Parameter polyC : forall (C2 : obC), forall (V : obV) (C1 : obC),
                          V(0 V |- C[0 C2 ~> C1 ]0 )0 ->
                          forall Y : obC, V(0 C[0 C1 ~> Y ]0  |- [0 V ~> C[0 C2 ~> Y ]0 ]0 )0.

      (** therefore "C[1 m ~> Y ]0" is similar to ( m o> _ ) **)
      Notation "C[1 m ~> Y ]0" := (@polyC _ _ _ m Y) (at level 25).

      (** therefore "C[0 Y ~> n ]1" is similar to the common ( _ <o n ) **)
      Notation "C[0 Y ~> n ]1" := (@polyC _ _ _ (@IdenV _) Y <o (n : V(0 _ |- C[0 _ ~> Y ]0 )0)) (at level 25).

      Definition polyC_IdenV : forall (D : obC), forall (C : obC),
                               forall X : obC, V(0 C[0 C ~> X ]0  |- [0 C[0 D ~> C ]0 ~> C[0 D ~> X ]0 ]0 )0
        := (fun D C X => @polyC D (C[0 D ~> C ]0) C (@IdenV (C[0 D ~> C ]0)) X).
      Notation "C[0 C ~> - ]1" := (@polyC_IdenV C) (at level 25).

      (** ** get some polymorph funtor F' **)

      Variable polyF'0 : obB -> obC.
      Notation "F'|0 B" := (polyF'0 B) (at level 4, right associativity).
      Notation "F'[0 C ~> B ]0" := (C[0 C ~> F'|0 B ]0) (at level 25).
      Parameter polyF' : forall (V : obV) (C : obC) (B : obB),
                           V(0 V |- F'[0 C ~> B ]0 )0 ->
                           forall X : obB, V(0 B[0 B ~> X ]0  |- [0 V ~> F'[0 C ~> X ]0 ]0 )0.
      Notation "F'[1 b ~> X ]0" := (@polyF' _ _ _ b X) (at level 25).
      Notation "F'[0 X ~> a ]1" := (@polyF' _ _ _ (@IdenV _) X <o (a : V(0 _ |- B[0 _ ~> X ]0 )0)) (at level 25).

      Definition polyF'_IdenV : forall (C : obC) (B : obB),
                                forall X : obB, V(0 B[0 B ~> X ]0  |- [0 F'[0 C ~> B ]0 ~> F'[0 C ~> X ]0 ]0 )0
        := (fun C B X => @polyF' (F'[0 C ~> B ]0) C B (@IdenV (F'[0 C ~> B ]0)) X).
      Notation "F'[0 C ~> - ]1" := (@polyF'_IdenV C) (at level 25).
      
      (**             c o>F'F a  =  c o>F' (1 o>F a)   ...   c o>F' (b o>F a) = (c o>F' b) o>F'F a ,       b : _ -> F _              
                         d o>F'' (c o>F' (b o>F a))              catA -> catB -> catC -> catD         **)
      Definition composition_F'_after_F :
        forall (V : obV) (B : obB) (A : obA),
        forall (b : V(0 V |- B[0 B ~> F|0 A ]0 )0),
        forall (W : obV) (C : obC),
        forall (c : V(0 W |- C[0 C ~> F'|0 B]0 )0),
        forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> [0 W ~> C[0 C ~> F'|0 F|0 X ]0 ]0 ]0 )0.
      Proof.
        intros.
        (*eapply ComV. ... not anymore that unitary is definationally same as identitary *)
        eapply polyV_relT_identitary (* _ <o _ *). apply consV01. apply (polyF' c).
        apply (polyF b).
(*        apply consV01.
        apply (polyF' c). *)
        Show Proof.
      (*
(fun (V : obV) (B : obB) (A : obA) (b : V(0 V |- F[0 B ~> A ]0 )0) 
   (W : obV) (C : obC) (c : V(0 W |- F'[0 C ~> B ]0 )0) 
   (X : obA) => [0V ~> F'[1 c ~> F|0 X ]0 ]1 <o F[1 b ~> X ]0) *)
      Defined.

      (************
       b : V( V |- B[ B ~> FA] )  ->
      a : B[ B ~> A[ A ~> X ] ] -> [V ~> B[ B ~> F X ]]

      _ o>B ((B[ b ~> FX ] <o F|1 A X) a)

      _ o>B  (b o>F a)

     (b' _j) o>B  ((b _i) o>F a)

                  _j |> ( (b _i) o> F (a _j) )  ....  (b _i) o>F a

      catA -> F: catB -> F': catC , and catA enriched in catB, and catB enriched in catC enriched in catV
      b : V(V |- C[ C |- B[ B ~> F A] ] )  ->
      a : C[ C ~> B[ B ~> A[ A ~> X ] ] ] -> [V ~> C[ C ~> B[ B ~> F X ]]]                                                                 
                 _j |> ( (b _i _i') o> F (a _i' _j) )  ....  (b _i _i') o>F a

      c : V( W |- C[ C' ~> F' B] )  ->
      b' : C[ C' ~> B[ B ~> Y ] ] -> [W ~> C[ C' ~> F' Y ]]

      given only map on objects F|0, F'|0, define any polyMorphism named polyG :
      b : V(V |- C[ C |- B[ B ~> F|0 A] ] )  ->
      c : V( W |- C[ C ~> F'|0 B] )  ->
      a : V( C[ C ~> B[ B ~> A[ A ~> X ] ] ] |- [V ~> [W ~> C[ C ~> F'|0 F|0 X ] ] ] )

       *****)                                              
      
      
      Parameter unitB : forall {B : obB}, V(0 I |- B[0 B ~> B ]0 )0.
      Notation "'uB'" := (@unitB _) (at level 0).

      Definition composition_F'_after_F_simple :
        forall  (A : obA),
        forall (W : obV) (C : obC),
        forall (c : V(0 W |- C[0 C ~> F'|0 F|0 A ]0 )0),
        forall X : obA, V(0 A[0 A ~> X ]0  |- [0 W ~> C[0 C ~> F'|0 F|0 X ]0 ]0 )0.
      Proof.
        intros.
        apply DesIdenObR.
        eapply composition_F'_after_F.
        eapply unitB.
        exact c.
        Show Proof.
      (*
(fun (A : obA) (W : obV) (C : obC) (c : V(0 W |- F'[0 C ~> F|0 A ]0 )0)
   (X : obA) => DesIdenObR (composition_F'_after_F uB c X))
       *)
      Defined.

      Notation "F'F|0 B" := (F'|0 F|0 B) (at level 4, right associativity).
      Notation "F'F[0 C ~> A ]0" := (C[0 C ~> F'F|0 A ]0) (at level 25).
      Notation "F'F[1 c ~> X ]0" := (@composition_F'_after_F _ _ _ c X) (at level 25).
      Notation "F'F[0 X ~> a ]1" := (@composition_F'_after_F _ _ _ (@IdenV _) X <o (a : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).

      Definition composition_F'_after_F_IdenV : forall (C : obC) (A : obA),
                                                forall X : obA, V(0 A[0 A ~> X ]0  |- [0 F'F[0 C ~> A ]0 ~> F'F[0 C ~> X ]0 ]0 )0
        := (fun C A X => @composition_F'_after_F_simple A (F'F[0 C ~> A ]0) C (@IdenV (F'F[0 C ~> A ]0)) X).
      Notation "F'F[0 C ~> - ]1" := (@composition_F'_after_F_IdenV C) (at level 25).

      Definition polyF_unitB : forall (A : obA),
                               forall X : obA, V(0 A[0 A ~> X ]0  |- B[0 F|0 A ~> F|0 X ]0 )0.
        intros.
        apply DesIdenObR.
        apply polyF.
        apply unitB.
        Show Proof.
        (* (fun A X : obA => DesIdenObR (F[1 uB ~> X ]0))  *)
      Defined.

      (* F|1 is internal structural arrow , but F[0 B ~> - ]1 are external structural arrows*)
      Notation "F|1" := (@polyF_unitB) (at level 0).

      Lemma composition_F'_after_F_identitary_polyF'_identitary_polyF_unitary :    forall (C : obC) (A X : obA),
                                                                                     (F'[0 C ~> - ]1) F|0 A F|0 X <o F|1 A X ~~ (F'F[0 C ~> - ]1) A X.
      Proof.
        intros.
        unfold composition_F'_after_F_IdenV.
        unfold composition_F'_after_F_simple.
        unfold composition_F'_after_F.
        unfold polyF'_IdenV.
        unfold polyF_unitB.
        apply SymV, DesIdenObR_output.
      Qed.
    (* apply this to unfold this as identitary (external-structural) of composition of polyfunctors ( polyV_relV o (poly_of_meta F[0 B ~> - ]1) ) .. ( polyV_relV o (poly_of_meta metaFB) )  ...  show before that
1. NEXT1 some metafunctor metaFB into catV on top of F[0 B ~> - ]1  by polyF which becomes  metaFB := meta_of_poly F at B,
2. then get derived polyfunctor from this metafunctor, 
3. then unitary( |1 ) of this derived polyfunctor is  identitary( ||1 ) of the metafunctor metaFB on top of F[0 B ~> - ]1 
4. NEXT2 which is  identitary ( [B ~> - ]1 ) of original polyfunctor F
 
all: ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o F[0 B ~> - ]1 A' X   
       ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o (meta_of_poly F at B)||1 A' X    
       ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o FB||1 A' X    
       ( V[0 V ~> - ]1 (F[0 B ~> A' ]0) (F[0 B ~> X ]0) ) <o (poly_of_meta metaFB)|1 A' X
       (polyV_relV o (poly_of_meta metaFB))[0 V ~> - ]1 A' X
       (meta_of_poly (polyV_relV o (poly_of_meta (meta_of_poly F at B))) at V)||1 A' X

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
      ... == natural_metatransformation from (meta_of_poly polyA at A) to (meta_of_poly (polyV_relV o (poly_of_meta (meta_of_poly F at B))) at V) by β at A' at X

NEXT3: naturality of any metatransformation of any metafunctors <-> polymorphism of coresp polytransformation of coresp polyfuntors
NEXT4: rewrite natural as above

     *)

      
      
    End  FunctorComposition.
    
    Section MetaTransformation.

      Section Meta_of_poly.
        
        (** ** meta_of_polyF_at_B , metafunctor FB on top of F[0 B ~> - ]1 **)

        Variable B : obB.

        Definition meta_of_polyF_at_B0 : obA -> obV
          := fun A : obA => F[0 B ~> A ]0 .
        Notation "FB|0 A" := (meta_of_polyF_at_B0 A) (at level 4, right associativity).

        Definition meta_of_polyF_at_B : forall (V : obV)  (A : obA),
                                          V(0 V |- FB|0 A )0 ->
                                          forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> FB|0 X ]0 )0
          := (fun (V : obV) (A : obA) (f : V(0 V |- FB|0 A )0) (X : obA) =>
                @polyF V B A f X (* F[1 f ~> X ]0 *) ) .
        (* intros. unfold meta_of_polyF_at_B0. apply polyF. assumption.
        Show Proof. *)

        Notation "FB[1I b ~> X ]0" := (@meta_of_polyF_at_B _ _ b X) (at level 25).

        Definition meta_of_polyF_at_B_IdenV : forall A X : obA, V(0 A[0 A ~> X ]0 |- [0 FB|0 A ~> FB|0 X ]0 )0
          :=  (fun A X => @meta_of_polyF_at_B _ A (@IdenV _) X).
        Notation "FB||1" := (@meta_of_polyF_at_B_IdenV _ _) (at level 0).

        Lemma  Cong_meta_of_polyF_at_B : forall (V : obV)(A : obA),
                                         forall (f f' : V(0 V |- FB|0 A )0),
                                           f' ~~ f -> forall X : obA, FB[1I f' ~> X ]0 ~~ FB[1I f ~> X ]0 .
        Proof.
          intros. unfold meta_of_polyF_at_B. apply CongPolyF. assumption.
        Qed.

        Lemma meta_of_polyF_at_B_arrow : forall (A : obA),
                                         forall (V V' : obV) (v : V(0 V' |- V )0),
                                         forall (f : V(0 V |- FB|0 A )0) (X : obA),
                                           FB[1I f <o v ~> X ]0
                                             ~~ [1 v ~> FB|0 X ]0 <o FB[1I f ~> X ]0 .
        Proof.
          unfold meta_of_polyF_at_B. apply polyF_arrow.
        Qed.

        Lemma meta_of_polyF_at_B_morphism : forall (V : obV),
                                            forall (A : obA) (W : obV) (A' : obA) (g : V(0 W |- A[0 A ~> A']0 )0),
                                            forall (f : V(0 V |-FB|0 A )0) (X : obA),
                                              FB[1I Des( [1 f ~> FB|0 A' ]0 <o (FB||1 <o g) ) ~> X]0
                                                ~~  DesIn( [0 W ~> FB[1I f ~> X ]0 ]1 ) <o A[1 g ~> X ]0 .
        Proof.
          unfold meta_of_polyF_at_B.  intros.
          (*TODO ERASE this line later *) eapply TransV; [eapply SymV, DesIn_Input|];
          apply polyF_morphism.
        Qed.

        (** related to non-variance when unit push the output, commonly  ( (f _i) o>FB 1 ) ~~ (f _i)  , 
       therefore metaFB is injective **)
        Lemma meta_of_polyF_at_B_inputUnitA : forall (V : obV) (A : obA),
                                      forall (f : V(0 V |- FB|0 A )0),
                                        f ~~ DesIdenObL( (FB[1I f ~> A ]0) <o (@unitA A) ).
        Proof.
          unfold meta_of_polyF_at_B. intros.
          apply polyF_inputUnitA.
        Qed.
                    
        Lemma meta_of_polyF_at_B_identitary_polyF_identitary : forall (A : obA),
                                                               forall X : obA,  FB||1 ~~ F[0 B ~> - ]1 A X .
        Proof. 
          unfold meta_of_polyF_at_B_IdenV. unfold meta_of_polyF_at_B. unfold polyF_IdenV .
          intros. apply ReflV.
        Qed.

      End Meta_of_poly.

      Section Poly_of_meta.

        (** ** poly_of_metaP of metaP **)
        
        Parameter metaP0 : obA -> obV.
        Notation "P|0 A" := (metaP0 A) (at level 4, right associativity).

        Parameter metaP : forall (V : obV) (A : obA),
                            V(0 V |- P|0 A )0 ->
                            forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> P|0 X ]0 )0.

        Notation "P[1I b ~> X ]0" := (@metaP _ _ b X) (at level 25).

        Definition metaP_IdenV : forall A X : obA, V(0 A[0 A ~> X ]0 |- [0 P|0 A ~> P|0 X ]0 )0
          :=  (fun A X => @metaP _ A (@IdenV _) X).
        Notation "P||1" := (@metaP_IdenV _ _) (at level 0).

        Hypothesis CongMetaP : forall (V : obV)(A : obA),
                               forall (f f' : V(0 V |- P|0 A )0),
                                 f' ~~ f -> forall X : obA, P[1I f' ~> X ]0 ~~ P[1I f ~> X ]0 .

        Hypothesis metaP_arrow : forall (A : obA),
                                 forall (V V' : obV) (v : V(0 V' |- V )0),
                                 forall (f : V(0 V |- P|0 A )0) (X : obA),
                                   P[1I f <o v ~> X ]0
                                    ~~ [1 v ~> P|0 X ]0 <o P[1I f ~> X ]0 .

        Hypothesis metaP_morphism : forall (V : obV),
                                    forall (A : obA) (W : obV) (A' : obA) (g : V(0 W |- A[0 A ~> A']0 )0),
                                    forall (f : V(0 V |-P|0 A )0) (X : obA),
                                      P[1I Des( [1 f ~> P|0 A' ]0 <o (P||1 <o g) ) ~> X]0
                                       ~~  DesIn( [0 W ~> P[1I f ~> X ]0 ]1 ) <o A[1 g ~> X ]0 .

        (** related to non-variance when unit push the output, commonly  ( (f _i) o>P 1 ) ~~ (f _i)  , 
       therefore metaP is injective **)
        Hypothesis metaP_inputUnitA : forall (V : obV) (A : obA),
                                      forall (f : V(0 V |- P|0 A )0),
                                        f ~~ DesIdenObL( (P[1I f ~> A ]0) <o (@unitA A) ).
        (*      (** ??? this is extra for metafunctor than polyfunctor : related to non-variance when unit pull the input, commonly  ( 1 o> h ) ~~ h     ....     ( 1 o> # ) ~~ #  ??? **)
      Hypothesis metaP_unitB : forall (B : obB), forall X : obA, (@IdenV (P[0 B ~> X ]0)) ~~ DesIdenObR( P[1I (@unitB B) ~> X ]0 ) .         *)
        Notation "P[0 B ~> A ]0" := (V[0 B ~> P|0 A ]0) (at level 25).
        Definition poly_of_metaP : forall (V : obV) (B : obV) (A : obA),
                                     V(0 V |- P[0 B ~> A ]0 )0 ->
                                     forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> P[0 B ~> X ]0 ]0 )0
          := fun (V B : obV) (A : obA) (b : V(0 V |- P[0 B ~> A ]0 )0) (X : obA) =>
               ConsIn (P[1I Des b ~> X ]0). 

        Notation "P[1 b ~> X ]0" := (@poly_of_metaP _ _ _ b X) (at level 25).
        Notation "P[0 X ~> a ]1" := (@poly_of_metaP _ _ _ (@IdenV _) X <o (a : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).

        Hypothesis Des_Input : forall (U U' : obV) (w : V(0 U' |- U )0), forall (V W : obV) (v : V(0 U |- [0 V ~> W ]0 )0), 
                                 Des( v <o w ) ~~ Des( v ) <o desV10 V w .
        Hypothesis ConsIn_Output : forall V : obV, forall (U0 : obV), forall (U1 U1' : obV) (u1 : V(0 U1' |- U1 )0), forall (W : obV), forall (v : V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0),
                                     ConsIn( [1 (1 u1 * V )0 ~> W ]0 <o v ) ~~ [1 u1 ~> [0 V ~> W ]0 ]0 <o ConsIn( v ) .
        Lemma poly_of_metaP_arrow : forall (B : obV) (A : obA),
                                    forall (V V' : obV) (v : V(0 V' |- V )0),
                                    forall (f : V(0 V |- P[0 B ~> A ]0 )0) (X : obA),
                                      P[1 f <o v ~> X ]0
                                       ~~ [1 v ~> P[0 B ~> X ]0 ]0 <o P[1 f ~> X ]0 .
        Proof.
          intros. unfold poly_of_metaP.
          eapply TransV; [| eapply CongConsIn, CongMetaP, Des_Input ].
          eapply TransV; [| eapply CongConsIn, metaP_arrow ].
          apply ConsIn_Output.
        Qed.

        Lemma Cong_poly_of_metaP : forall (V : obV) (B : obV) (A : obA),
                                   forall (f f' : V(0 V |- P[0 B ~> A ]0 )0),
                                     f' ~~ f -> forall X : obA, P[1 f' ~> X ]0 ~~ P[1 f ~> X ]0.
        Proof.
          intros. unfold poly_of_metaP.  apply CongConsIn, CongMetaP, CongDes. assumption.
        Qed.

        Hypothesis CongConsV01 : forall V1 : obV, forall (V2 V2' : obV) (v v' : V(0 V2 |- V2' )0),
                                   v' ~~ v -> [0 V1 ~> v' ]1 ~~ [0 V1 ~> v ]1 .
        Hypothesis ConsIn_Input : forall V : obV, forall (U0 U1 W : obV), forall (v : V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0), forall (U0' : obV) (i : V(0 U0' |- U0 )0),
                                    ConsIn( v <o i ) ~~ (ConsIn v) <o i .
        Hypothesis consV01_functorial : forall V1 : obV, forall V2 V2' (v : V(0 V2 |- V2' )0), forall V2'' (v' : V(0 V2' |- V2'' )0),
                                          [0 V1 ~> v' <o v ]1 ~~  [0 V1 ~> v' ]1 <o  [0 V1  ~> v ]1 .
        Parameter Cons : forall V : obV, forall (U W : obV), V(0 (0 U * V )0 |-  W )0 -> V(0 U |-  [0 V ~> W ]0 )0.
        Hypothesis CongCons : forall V : obV, forall (U W : obV), forall (v v' : V(0 (0 U * V )0 |- W )0 ),
                                v' ~~ v -> Cons v' ~~ Cons v.
        Hypothesis Cons_Des : forall V : obV, forall (U W : obV), forall (f : V(0 U |-  [0 V ~> W ]0 )0),
                                Cons (Des f) ~~ f.
        Hypothesis Cons_Input : forall V : obV, forall (U U' : obV) (w : V(0 U' |- U )0), forall (W : obV) (v : V(0 (0 U * V )0 |- W )0),
                                  Cons(v <o desV10 V w)  ~~ Cons( v ) <o w .
        Hypothesis DesIn_ConsIn : forall V : obV, forall (U0 U1 W : obV), forall (f : V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0),
                                    DesIn (ConsIn f) ~~ f.

        Parameter Assoc : forall {V W : obV}, forall {U: obV}, V(0 (0 U * (0 V * W )0 )0 |- (0 ((0 U * V )0) * W )0 )0.
        Hypothesis Assoc_Iso : forall (V W : obV), forall (U: obV),
                               forall (Y X : obV) (f g : V(0 Y |-  [0 (0 ((0 U * V )0) * W )0 ~> X ]0 )0 ), 
                                 [1 Assoc ~> X ]0 <o f ~~ [1 Assoc  ~> X ]0 <o g -> f ~~ g .
        Hypothesis Assoc_nat0 : forall (V W : obV), forall (U U' : obV) (f : V(0 U |- U' )0 ),
                                  Assoc <o (1 f * (0 V * W )0 )0 ~~ (1 ((1 f * V )0) * W )0 <o Assoc .
        Hypothesis Des_consV10_functorial : forall V B PA (f : V(0 V |- [0 B ~> PA ]0 )0) PA' QA (g : V(0 [0 B ~> PA ]0 |- [0 B ~> QA ]0 )0) ,
                                              (Des ([1 Des (g <o f) ~> PA' ]0 ))
                                                ~~ ( ( Des (Des ([1 f ~> [0 B ~> PA' ]0 ]0 <o ConsIn ([1 Des (g) ~> PA' ]0))) ) <o Assoc
                                                     : V(0 (0 ([0 QA ~> PA' ]0) * (0V * B )0 )0 |- PA' )0 ).
        (** Hypothesis Assoc_Des_Des_old : forall V B PA PA' (f : V(0 V |- [0 B ~> PA ]0 )0),
                                     ( (Des ([1 Des f ~> PA' ]0 )) : V(0 (0 ([0 PA ~> PA' ]0) * (0V * B )0 )0 |- PA' )0 )
                                       ~~ ( ( Des (Des ([1 f ~> [0 B ~> PA' ]0 ]0 <o ConsIn ([1 Des (@IdenV ([0 B ~> PA ]0)) ~> PA' ]0))) ) <o Assoc ). **)
        Hypothesis Assoc_DesIn_DesIn :  forall W PX, forall  V B PA (f : V(0 V |- [0 B ~> PA ]0 )0),
                                          DesIn ([0 W ~>  ([1 Des f ~> PX ]0) ]1)
                                                ~~ [1 Assoc ~> PX ]0 <o DesIn( DesIn ([0 W ~>  ConsIn([1 Des f ~> PX ]0) ]1) ) .

        Lemma poly_of_metaP_morphism : forall (B : obV) (V : obV),
                                       forall (A : obA) (W : obV) (A' : obA) (g : V(0 W |- A[0 A ~> A']0 )0),
                                       forall (f : V(0 V |-P[0 B ~> A ]0 )0) (X : obA),
                                         P[1 Des( [1 f ~> P[0 B ~> A' ]0 ]0 <o P[0 A' ~> g ]1 ) ~> X ]0
                                          ~~  DesIn( [0 W ~> P[1 f ~> X ]0 ]1 ) <o A[1 g ~> X ]0.
        Proof.
          (* enough (  [1Assoc ~> P|0 X ]0 <o DesIn ( _ ) ~~  [1Assoc ~> P|0 X ]0 <o DesIn ( _ ) ) *)
          intros. unfold poly_of_metaP.
          intros;  eapply TransV; [ eapply TransV | ]; [ apply ConsIn_DesIn | idtac | apply SymV, ConsIn_DesIn].
          apply CongConsIn, Assoc_Iso.

          (** LHS **)
          eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply DesIn_ConsIn].
          eapply TransV; [| eapply SymV, metaP_arrow ].
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply CongConsIn, CongMetaP, Cat1LeftV | eapply ReflV]  ] | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply CongConsIn, metaP_arrow | eapply ReflV]  ] | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply ConsIn_Input | eapply ReflV]  ] | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply Cat2V  ] | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply CongDes, CongDes, SymV, Cat2V  | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply CongDes, Des_Input  | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply Des_Input  | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaP, Cat2V ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply ReflV | eapply SymV, Assoc_nat0 ] ] .
          eapply TransV; [| eapply CongMetaP, SymV, Cat2V ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [ eapply SymV, Des_consV10_functorial  | eapply ReflV] ] .
          eapply TransV; [| eapply CongMetaP, CongCom; [|eapply ReflV]; eapply CongDes, CongConsV10, CongDes, SymV, Cat1LeftV ] .
          eapply TransV; [| eapply CongMetaP, SymV, Des_Input ] .

          (** RHS **)
          eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply DesIn_Input |].
          eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongDesIn, CongConsV01, CongConsIn, CongMetaP, SymV, Cat1LeftV |].
          eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongDesIn, CongConsV01, CongConsIn, SymV, metaP_arrow  |].
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
          eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongConsV01, metaP_arrow  |].
          eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongConsV01, CongMetaP, Cat1LeftV  |].

          eapply metaP_morphism.
        Qed.
        
        Definition poly_of_metaP_IdenV : forall (B : obV) (A : obA),
                                         forall X : obA, V(0 A[0 A ~> X ]0  |- [0 P[0 B ~> A ]0 ~> P[0 B ~> X ]0 ]0 )0
          := (fun B A X => @poly_of_metaP (P[0 B ~> A ]0) B A (@IdenV (P[0 B ~> A ]0)) X).
        Notation "P[0 B ~> - ]1" := (@poly_of_metaP_IdenV B) (at level 25).

        (** ** unit part of above get that the logical category V is polymorph **)

        Parameter unitV : forall {A : obV}, V(0 I |- V[0 A ~> A ]0 )0.
        Notation "'uV'" := (@unitV _) (at level 0).

        Hypothesis unitV_IdenV : forall A : obV,  (@IdenV A) ~~ DesIdenObL (@unitV A).

        Hypothesis polyV_relV_unitV : forall (A : obV), forall X : obV, (@IdenV (V[0 A ~> X ]0)) ~~ DesIdenObR( V[1 (@unitV A) ~> X ]0 ) .

        Hypothesis polyV_relV_inputUnitV : forall (B : obV), forall (V : obV) (A : obV),
                                      forall (f : V(0 V |- V[0 B ~> A ]0 )0),
                                        f  ~~ DesIdenObL( (V[1 f ~> A ]0) <o (@unitV A) ).

        (** already ConsIn_Input above **)
        Hypothesis DesIdenObR_Input : forall (U W : obV) (U' : obV) (w : V(0 U' |- U )0), forall v : V(0 U |- [0 I ~> W ]0 )0, 
                                        DesIdenObR( v <o w ) ~~ DesIdenObR( v ) <o w .

        Hypothesis consV10_DesIdenObL : forall U : obV, forall V : obV, forall (W : obV), forall (v : V(0 I |- [0 V ~> W ]0 )0), 
                                          [1 DesIdenObL  v ~> U ]0  ~~ DesIdenObR( ConsIn( [1 Des v ~> U ]0 ) ) .

        Hypothesis consV10_functorial_fun1 : forall V1, forall V2 : obV,
                                               (@IdenV _) ~~    [1 (@IdenV V1) ~> V2 ]0 .

        (** ** continue poly_of_metaP of metaP **)

        Definition poly_of_metaP_unitV : forall (A : obA),
                                         forall X : obA, V(0 A[0 A ~> X ]0  |- [0 P|0 A ~> P|0 X ]0 )0
          := (fun A X => DesIdenObR(@poly_of_metaP I (P|0 A) A (@unitV _) X)).
        Notation "P|1" := (@poly_of_metaP_unitV _ _) (at level 0).
        
        (** poly_of_metaP_unitV_metaP_IdenV : forall A X : obA, P|1 ~~ P||1 **)
        Lemma poly_of_metaP_unitV_metaP_IdenV : forall A X : obA, 
                                                  @poly_of_metaP_unitV A X ~~ @metaP_IdenV A X .
        Proof.
          intros.
          unfold poly_of_metaP_unitV. unfold poly_of_metaP.
          unfold metaP_IdenV.
          eapply TransV; cycle 1.
          eapply CongDesIdenObR, CongConsIn, CongMetaP, Cat1LeftV .
          eapply TransV; [| eapply CongDesIdenObR, CongConsIn, metaP_arrow ].
          eapply TransV; [| eapply CongDesIdenObR, ConsIn_Input ].
          eapply TransV; [| eapply DesIdenObR_Input ].
          eapply TransV; [| eapply CongCom; [eapply SymV, consV10_DesIdenObL | eapply ReflV] ].
          eapply TransV; [| eapply CongCom; [ eapply CongConsV10, SymV, unitV_IdenV  | eapply ReflV] ].
          eapply TransV; [| eapply CongCom; [ eapply SymV, consV10_functorial_fun1  | eapply ReflV] ].
          eapply SymV, Cat1LeftV.
        Qed.

        (** ** poly_of_metaQ of metaQ **)

        Parameter metaQ0 : obA -> obV.
        Notation "Q|0 A" := (metaQ0 A) (at level 4, right associativity).

        Parameter metaQ : forall (V : obV) (A : obA),
                            V(0 V |- Q|0 A )0 ->
                            forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> Q|0 X ]0 )0.

        Notation "Q[1I b ~> X ]0" := (@metaQ _ _ b X) (at level 25).

        Definition metaQ_IdenV : forall A X : obA, V(0 A[0 A ~> X ]0 |- [0 Q|0 A ~> Q|0 X ]0 )0
          :=  (fun A X => @metaQ _ A (@IdenV _) X).
        Notation "Q||1" := (@metaQ_IdenV _ _) (at level 0).

        Hypothesis CongMetaQ : forall (V : obV)(A : obA),
                               forall (f f' : V(0 V |- Q|0 A )0),
                                 f' ~~ f -> forall X : obA, Q[1I f' ~> X ]0 ~~ Q[1I f ~> X ]0 .

        Hypothesis metaQ_arrow : forall (A : obA),
                                 forall (V V' : obV) (v : V(0 V' |- V )0),
                                 forall (f : V(0 V |- Q|0 A )0) (X : obA),
                                   Q[1I f <o v ~> X ]0
                                    ~~ [1 v ~> Q|0 X ]0 <o Q[1I f ~> X ]0 .

        Hypothesis metaQ_morphism : forall (V : obV),
                                    forall (A : obA) (W : obV) (A' : obA) (g : V(0 W |- A[0 A ~> A']0 )0),
                                    forall (f : V(0 V |-Q|0 A )0) (X : obA),
                                      Q[1I Des( [1 f ~> Q|0 A' ]0 <o (Q||1 <o g) ) ~> X]0
                                       ~~  DesIn( [0 W ~> Q[1I f ~> X ]0 ]1 ) <o A[1 g ~> X ]0 .

        (** related to non-variance when unit push the output, commonly  ( (f _i) o>Q 1 ) ~~ (f _i)  , 
       therefore metaQ is injective **)
        Hypothesis metaQ_inputUnitA : forall (V : obV) (A : obA),
                                      forall (f : V(0 V |- Q|0 A )0),
                                        f ~~ DesIdenObL( (Q[1I f ~> A ]0) <o (@unitA A) ).
        (*      (** ??? this is extra for metafunctor than polyfunctor : related to non-variance when unit pull the input, commonly  ( 1 o> h ) ~~ h     ....     ( 1 o> # ) ~~ #  ??? **)
      Hypothesis metaQ_unitB : forall (B : obB), forall X : obA, (@IdenV (Q[0 B ~> X ]0)) ~~ DesIdenObR( Q[1I (@unitB B) ~> X ]0 ) .         *)
        Notation "Q[0 B ~> A ]0" := (V[0 B ~> Q|0 A ]0) (at level 25).
        Definition poly_of_metaQ : forall (V : obV) (B : obV) (A : obA),
                                     V(0 V |- Q[0 B ~> A ]0 )0 ->
                                     forall X : obA, V(0 A[0 A ~> X ]0  |- [0 V ~> Q[0 B ~> X ]0 ]0 )0
          := fun (V B : obV) (A : obA) (b : V(0 V |- Q[0 B ~> A ]0 )0) (X : obA) =>
               ConsIn (Q[1I Des b ~> X ]0). 

        Notation "Q[1 b ~> X ]0" := (@poly_of_metaQ _ _ _ b X) (at level 25).
        Notation "Q[0 X ~> a ]1" := (@poly_of_metaQ _ _ _ (@IdenV _) X <o (a : V(0 _ |- A[0 _ ~> X ]0 )0)) (at level 25).

        Lemma poly_of_metaQ_arrow : forall (B : obV) (A : obA),
                                    forall (V V' : obV) (v : V(0 V' |- V )0),
                                    forall (f : V(0 V |- Q[0 B ~> A ]0 )0) (X : obA),
                                      Q[1 f <o v ~> X ]0
                                       ~~ [1 v ~> Q[0 B ~> X ]0 ]0 <o Q[1 f ~> X ]0 .
        Proof.
          intros. unfold poly_of_metaQ.
          eapply TransV; [| eapply CongConsIn, CongMetaQ, Des_Input ].
          eapply TransV; [| eapply CongConsIn, metaQ_arrow ].
          apply ConsIn_Output.
        Qed.

        Lemma Cong_poly_of_metaQ : forall (V : obV) (B : obV) (A : obA),
                                   forall (f f' : V(0 V |- Q[0 B ~> A ]0 )0),
                                     f' ~~ f -> forall X : obA, Q[1 f' ~> X ]0 ~~ Q[1 f ~> X ]0.
        Proof.
          intros. unfold poly_of_metaQ.  apply CongConsIn, CongMetaQ, CongDes. assumption.
        Qed.

        Lemma poly_of_metaQ_morphism : forall (B : obV) (V : obV),
                                       forall (A : obA) (W : obV) (A' : obA) (g : V(0 W |- A[0 A ~> A']0 )0),
                                       forall (f : V(0 V |-Q[0 B ~> A ]0 )0) (X : obA),
                                         Q[1 Des( [1 f ~> Q[0 B ~> A' ]0 ]0 <o Q[0 A' ~> g ]1 ) ~> X ]0
                                          ~~  DesIn( [0 W ~> Q[1 f ~> X ]0 ]1 ) <o A[1 g ~> X ]0.
        Proof.
          (* enough (  [1Assoc ~> Q|0 X ]0 <o DesIn ( _ ) ~~  [1Assoc ~> Q|0 X ]0 <o DesIn ( _ ) ) *)
          intros. unfold poly_of_metaQ.
          intros;  eapply TransV; [ eapply TransV | ]; [ apply ConsIn_DesIn | idtac | apply SymV, ConsIn_DesIn].
          apply CongConsIn, Assoc_Iso.

          (** LHS **)
          eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply DesIn_ConsIn].
          eapply TransV; [| eapply SymV, metaQ_arrow ].
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply CongConsIn, CongMetaQ, Cat1LeftV | eapply ReflV]  ] | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply CongConsIn, metaQ_arrow | eapply ReflV]  ] | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply CongCom; [ eapply ConsIn_Input | eapply ReflV]  ] | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply CongDes, CongDes, CongCom; [ eapply ReflV | eapply Cat2V  ] | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply CongDes, CongDes, SymV, Cat2V  | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply CongDes, Des_Input  | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply Des_Input  | eapply ReflV ] ] .
          eapply TransV; [| eapply CongMetaQ, Cat2V ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply ReflV | eapply SymV, Assoc_nat0 ] ] .
          eapply TransV; [| eapply CongMetaQ, SymV, Cat2V ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [ eapply SymV, Des_consV10_functorial  | eapply ReflV] ] .
          eapply TransV; [| eapply CongMetaQ, CongCom; [|eapply ReflV]; eapply CongDes, CongConsV10, CongDes, SymV, Cat1LeftV ] .
          eapply TransV; [| eapply CongMetaQ, SymV, Des_Input ] .

          (** RHS **)
          eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply DesIn_Input |].
          eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongDesIn, CongConsV01, CongConsIn, CongMetaQ, SymV, Cat1LeftV |].
          eapply TransV; [eapply CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongDesIn, CongConsV01, CongConsIn, SymV, metaQ_arrow  |].
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
          eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongConsV01, metaQ_arrow  |].
          eapply TransV; [eapply CongCom; [|eapply ReflV]; eapply CongDesIn, CongConsV01, CongMetaQ, Cat1LeftV  |].

          eapply metaQ_morphism.
        Qed.
        
        Definition poly_of_metaQ_IdenV : forall (B : obV) (A : obA),
                                         forall X : obA, V(0 A[0 A ~> X ]0  |- [0 Q[0 B ~> A ]0 ~> Q[0 B ~> X ]0 ]0 )0
          := (fun B A X => @poly_of_metaQ (Q[0 B ~> A ]0) B A (@IdenV (Q[0 B ~> A ]0)) X).
        Notation "Q[0 B ~> - ]1" := (@poly_of_metaQ_IdenV B) (at level 25).

        (** ** continue poly_of_metaQ of metaQ **)

        Definition poly_of_metaQ_unitV : forall (A : obA),
                                         forall X : obA, V(0 A[0 A ~> X ]0  |- [0 Q|0 A ~> Q|0 X ]0 )0
          := (fun A X => DesIdenObR(@poly_of_metaQ I (Q|0 A) A (@unitV _) X)).
        Notation "Q|1" := (@poly_of_metaQ_unitV _ _) (at level 0).
        
        (** poly_of_metaQ_unitV_metaQ_IdenV : forall A X : obA, Q|1 ~~ Q||1 **)
        Lemma poly_of_metaQ_unitV_metaQ_IdenV : forall A X : obA, 
                                                  @poly_of_metaQ_unitV A X ~~ @metaQ_IdenV A X .
        Proof.
          intros.
          unfold poly_of_metaQ_unitV. unfold poly_of_metaQ.
          unfold metaQ_IdenV.
          eapply TransV; cycle 1.
          eapply CongDesIdenObR, CongConsIn, CongMetaQ, Cat1LeftV .
          eapply TransV; [| eapply CongDesIdenObR, CongConsIn, metaQ_arrow ].
          eapply TransV; [| eapply CongDesIdenObR, ConsIn_Input ].
          eapply TransV; [| eapply DesIdenObR_Input ].
          eapply TransV; [| eapply CongCom; [eapply SymV, consV10_DesIdenObL | eapply ReflV] ].
          eapply TransV; [| eapply CongCom; [ eapply CongConsV10, SymV, unitV_IdenV  | eapply ReflV] ].
          eapply TransV; [| eapply CongCom; [ eapply SymV, consV10_functorial_fun1  | eapply ReflV] ].
          eapply SymV, Cat1LeftV.
        Qed.

        
        (** ** now natural metatransformation **)

        Parameter metaβ : forall (A : obA),
                            V(0 P|0 A |- Q|0 A )0.

        Notation "β||0 A" := (@metaβ A) (at level 4, right associativity).

        (** written here : (inner modification) ~~ (outer modification)**)
        Hypothesis metaβ_morphism : forall (A : obA)  (A' : obA),
                                      [0 P|0 A ~>  β||0 A' ]1 <o P||1
                                                                ~~ [1 β||0 A ~> Q|0 A' ]0 <o Q||1.

        (** Cons et al was here , Des_Input was here **)

        Definition poly_of_metaβ : forall (V : obV) (B : obV) (A : obA),
                                     V(0 V |- P[0 B ~> A ]0 )0 ->
                                     V(0 V |- Q[0 B ~> A ]0 )0
          := fun (V B : obV) (A : obA) (b : V(0 V |- P[0 B ~> A ]0 )0) =>
               Cons (β||0 A <o Des b) .
        
        (** :^) **)
        Notation "β|1 f" := (@poly_of_metaβ _ _ _ f) (at level 5, right associativity).
        (** this Notation "β|0 A" is not held below **)
        Notation "β|0 A" := (@poly_of_metaβ _ _ A (@IdenV _)) (at level 4, right associativity).

        Lemma poly_of_metaβ_arrow : forall (B : obV) (A : obA),
                                    forall (V V' : obV) (v : V(0 V' |- V )0),
                                    forall (f : V(0 V |- P[0 B ~> A ]0 )0) (X : obA),
                                      β|1 (f <o v)
                                          ~~ β|1 f <o v .
        Proof.
          intros.
          unfold poly_of_metaβ.
          eapply TransV; [ eapply Cons_Input  |] .
          eapply TransV; [ eapply CongCons; eapply SymV, Cat2V  |] .
          eapply TransV; [ eapply CongCons; eapply CongCom; [ eapply ReflV |  eapply Des_Input  ] |] .
          eapply ReflV.
        Qed.

        Hypothesis Cons_Output : forall V : obV, forall (U W : obV), forall (v :  V(0 (0 U * V )0 |-  W )0), forall W' (w : V(0 W |- W' )0),
                                   [0 V ~> w ]1 <o Cons( v ) ~~ Cons( w <o v ) .
        Hypothesis Des_Output : forall V : obV, forall (U W : obV), forall (v : V(0 U |- [0 V ~> W ]0 )0), forall W' (w : V(0 W |- W' )0),
                                  Des( [0 V ~> w ]1 <o v ) ~~ w <o Des( v ) .
        Hypothesis ConsIn_Output2 : forall V : obV, forall (U0 : obV), forall (U1 : obV) , forall (W W' : obV) (w : V(0 W |- W' )0), forall (v : V(0 U0 |- [0 (0 U1 * V )0 ~> W ]0 )0),
                                      ConsIn( [0 (0 U1 * V )0 ~> w ]1 <o v ) ~~ [0 U1 ~> [0 V ~> w ]1 ]1 <o ConsIn( v ) .
        Hypothesis ConsIn_consV10_functorial : forall V B PA (f : V(0 V |- [0 B ~> PA ]0 )0) PA' QA (g : V(0 [0 B ~> PA ]0 |- [0 B ~> QA ]0 )0),
                                                 ( ConsIn (([1 Des (g <o f) ~> PA' ]0)) )
                                                   ~~ ( ([1 f ~> [0 B ~> PA' ]0 ]0 <o ConsIn ([1 Des (g) ~> PA' ]0))
                                                        : V(0 [0 QA ~> PA' ]0 |- [0 V ~> [0 B ~> PA' ]0 ]0 )0 ) .
        Hypothesis Des_Cons : forall V : obV, forall (U W : obV), forall (f : V(0 (0 U * V )0 |-  W )0),
                                Des (Cons f) ~~ f.
        
        (** ?? may change def of funtor into V because now extra decoding while already in V ?? **)
        (** written here : (inner modification) ~~ (outer modification)**)
        Lemma poly_of_metaβ_morphism : forall (V : obV) (B : obV),
                                       forall (A : obA) (W : obV) (A' : obA) (a : V(0 W |- A[0 A ~> A']0 )0),
                                       forall (f : V(0 V |- P[0 B ~> A ]0 )0),
                                         β|1 (Des( [1 f ~> P[0 B ~> A' ]0 ]0 <o P[0 A' ~> a ]1 ))
                                             ~~ (Des( [1 β|1 f ~> Q[0 B ~> A' ]0 ]0 <o Q[0 A' ~> a ]1 )) .
        Proof.
          (** LHS **)
          intros. unfold poly_of_metaβ. unfold poly_of_metaP. unfold poly_of_metaQ.
          eapply TransV; [| eapply SymV, Cons_Output ].
          eapply TransV; [| eapply CongCom; [eapply ReflV| eapply Cons_Des] ].
          eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongConsIn, CongMetaP, Cat1LeftV ].
          eapply TransV; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongCom; [eapply ReflV|]; eapply CongCom; [|eapply ReflV]; eapply CongConsIn, metaP_arrow ].
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
          eapply TransV; [ eapply CongCom; [eapply ReflV|];  eapply CongConsIn , CongMetaQ, SymV, Cat1LeftV |].
          eapply TransV; [ eapply CongCom; [eapply ReflV|];  eapply CongConsIn , SymV, metaQ_arrow |].
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

        Lemma poly_of_metaβ_morphism_codomain : forall (V : obV),
                                                forall (B : obV) (W : obV) (B' : obV) (b : V(0 W |- V[0 B' ~> B]0 )0),
                                                forall (A : obA),
                                                forall (f : V(0 V |-P[0 B ~> A ]0 )0),
                                                  β|1 (Des( V[1 b ~> P|0 A ]0 <o f ))
                                                      ~~  Des( V[1 b ~> Q|0 A ]0 <o β|1 f ).
        Proof.
          (** LHS **)
          intros. unfold poly_of_metaβ.
          eapply TransV; [| eapply SymV, Cons_Output ].
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

        Hypothesis Des_I_Iso : forall (A : obV),
                               forall (Y X : obV) (f g : V(0 Y |-  [0  A ~> X ]0 )0 ), 
                                 [1 Des (@IdenV ([0 I ~> A ]0)) ~> X ]0 <o f ~~ [1  Des (@IdenV ([0 I ~> A ]0))  ~> X ]0 <o g -> f ~~ g .

        Lemma meta_morphism_of_poly_of_metaβ : ( forall (V : obV) (B : obV),
                                                 forall (A : obA) (W : obV) (A' : obA) (a : V(0 W |- A[0 A ~> A']0 )0),
                                                 forall (f : V(0 V |- P[0 B ~> A ]0 )0),
                                                   β|1 (Des( [1 f ~> P[0 B ~> A' ]0 ]0 <o P[0 A' ~> a ]1 ))
                                                       ~~ (Des( [1 β|1 f ~> Q[0 B ~> A' ]0 ]0 <o Q[0 A' ~> a ]1 )) )
                                               -> ( forall (A : obA)  (A' : obA),
                                                     [0 P|0 A ~>  β||0 A' ]1 <o P||1
                                                                               ~~ [1 β||0 A ~> Q|0 A' ]0 <o Q||1 ) .
        Proof.
          (** LHS **)
          intro H_poly_morphism. intros.
          specialize H_poly_morphism with (B := I) (A := A) (A' := A') (a := 1) (f := 1).
          unfold poly_of_metaβ in H_poly_morphism. unfold poly_of_metaP in H_poly_morphism. unfold poly_of_metaQ in H_poly_morphism.
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply SymV, Cons_Output ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply Cons_Des ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongCom; [|eapply ReflV]; eapply SymV, consV10_functorial_fun1 ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, SymV, Cat1LeftV ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, SymV, Cat1RightV ]. 
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongConsIn, CongMetaP, Cat1LeftV ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, CongConsIn, metaP_arrow ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|]; eapply CongDes, ConsIn_Input ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply SymV, Des_Output ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongDes, SymV, Cat2V ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongDes, CongCom; [|eapply ReflV]; eapply SymV, ConsIn_Output2   ].
          eapply SymV, TransV, SymV in H_poly_morphism; [| eapply CongDes, SymV, ConsIn_Input   ].

          (** RHS **)
          eapply CongCons in H_poly_morphism.
          eapply SymV, TransV, SymV in H_poly_morphism; [|eapply Cons_Des]. eapply TransV in H_poly_morphism; [|eapply Cons_Des].
          eapply  TransV in H_poly_morphism; [|eapply CongCom; [eapply ReflV|]; eapply SymV, Cat1RightV ].
          eapply TransV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|];  eapply CongConsIn, CongMetaQ, Cat1LeftV ].
          eapply TransV in H_poly_morphism; [| eapply CongCom; [eapply ReflV|];  eapply CongConsIn, metaQ_arrow].
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
        
      End Poly_of_meta.

    End MetaTransformation.

    Module NaturalityIsPolymorphic.


      
    End NaturalityIsPolymorphic.

    Module PolymorphismIsNaturalitywithinGallina.

    End  PolymorphismIsNaturalitywithinGallina.
      
    End NaturalityIsPolymorphic.

  End Transformation.

End Functor.
