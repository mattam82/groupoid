(** printing ~1 $\sim_1$ *)
(** printing ~ $\sim_2$ *)
(** printing ~2 $\sim_2$ *)
(** printing Π1 $\pi_1$*)
(** printing Π2 $\pi_2$*)
(** printing Πi $\pi_i$*)
(** printing --> $\longrightarrow$*)
(** printing ---> $\longrightarrow$*)
(** printing β $\beta$*)
(** printing χ $\chi$*)
(** printing [! $\llbracket$*)
(** printing !] $\rrbracket$*)
(** printing |- $\vdash$*)
(** printing === $\equiv$*)
(** printing @ $\star$*)
(** printing ° $\circ$*)
(** printing Category_1 $\mathrm{Category}_1$*)
(** printing Category_2 $\mathrm{Category}_2$*)
(** printing CategoryP $\mathrm{Category}$*)
(** printing GroupoidP $\mathrm{Groupoid}$*)
(** printing Groupoid_1 $\mathrm{Groupoid}_1$*)
(** printing Groupoid_2 $\mathrm{Groupoid}_2$*)
(** printing Equivalence_2 $\mathrm{Equivalence}_2$*)
(** printing Hom1 $\mathrm{Hom}_1$*)
(** printing Hom2 $\mathrm{Hom}_2$*)
(** printing Hom3 $\mathrm{Hom}_3$*)
(** printing _adjoint $\mathrm{adjoint}$*)
(** printing _section $\mathrm{section}$*)
(** printing _retraction $\mathrm{retraction}$*)
(** printing _triangle $\mathrm{triangle}$*)
(** printing nat_comp' $\mathrm{comp}$*)
(** printing _α_map $\mathrm{α}_\mathrm{map}$*)
(** printing _α_Dmap $\mathrm{α}_{\mathrm{map}^\Pi}$*)
(** printing α_map $\mathrm{α}_\mathrm{map}$*)
(** printing α_Dmap $\mathrm{α}_{\mathrm{map}^\Pi}$*)
(** printing _eq_section $\mathrm{eq\_section}$*)
(** printing _eq_retraction $\mathrm{eq\_retraction}$*)
(** printing Prod_Type $\Pi_\mathrm{T}$*)
(** printing _Prod $\Pi$*)
(** printing _Sum $\Sigma$*)
(** printing sum_type $\Sigma_\mathrm{T}$*)
(** printing sum_eq $\Sigma_\mathrm{Eq}$*)
(** printing sum_eq2 $\Sigma_{\mathrm{Eq}_2}$*)
(** printing eq2 $\mathrm{eq}_2$*)
(** printing eq1 $\mathrm{eq}_1$*)
(** printing HomT2 $\mathrm{HomT}_2$*)
(** printing HomT1 $\mathrm{HomT}_1$*)
(** printing id_R $\mathrm{id}_R$*)
(** printing id_L $\mathrm{id}_L$*)
(** printing inv_R $\mathrm{inv}_R$*)
(** printing inv_L $\mathrm{inv}_L$*)
(** printing ^-1 $\hspace{-1ex}^{-1}$*)
(** printing Trunc_2 $\mathrm{Trunc}_2$*)
(** printing map_id $\mathrm{map}_\mathrm{id}$*)
(** printing map_comp $\mathrm{map}_\mathrm{comp}$*)
(** printing map2 $\mathrm{map}_2$*)
(** printing _map $\mathrm{map}$*)
(** printing _map_id $\mathrm{map}_\mathrm{id}$*)
(** printing _map_comp $\mathrm{map}_\mathrm{comp}$*)
(** printing _map2 $\mathrm{map}_2$*)
(** printing map1 $\mathrm{map}_1$*)
(** printing Dmap $\mathrm{map}^\Pi$*)
(** printing _Dmap $\mathrm{map}^\Pi$*)
(** printing Dmap_id $\mathrm{map}^\Pi_\mathrm{id}$*)
(** printing Dmap_comp $\mathrm{map}^\Pi_\mathrm{comp}$*)
(** printing Dmap2 $\mathrm{map}^\Pi_2$*)
(** printing _Dmap_id $\mathrm{map}^\Pi_\mathrm{id}$*)
(** printing _Dmap_comp $\mathrm{map}^\Pi_\mathrm{comp}$*)
(** printing _Dmap2 $\mathrm{map}^\Pi_2$*)
(** printing Dmap1 $\mathrm{map}^\Pi_1$*)
(** printing DependentFunctor $\mathrm{Functor}^\Pi$*)
(** printing WeakDependentFunctor $\mathrm{WeakFunctor}^\Pi$*)
(** printing DNaturalTransformation $\mathrm{NaturalTransformation}^\Pi$*)
(** printing Dnat_trans $\mathrm{nat\_trans}^\Pi$*)
(** printing Dmodification $\mathrm{modification}^\Pi$*)
(** printing WeakGroupoidType $\mathrm{WeakGroupoidT}$*)
(** printing sum_weakgroupoid $\Sigma_\mathrm{WG}$*)
(** printing prod_weakgroupoid $\Pi_\mathrm{WG}$*)
(** printing IrrRelWeakGroupoid $\mathrm{IrrRelWG}$*)
(** printing Hom_irr $\mathrm{HomIrr}$*)

(* begin hide *)

Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
(* Require Import Setoid. *)
Set Universe Polymorphism.
Set Primitive Projections.
Definition id {A : Type} (a : A) := a.

Arguments id /.

Record sigma {A : Type} (P : A -> Type) :=
  { proj1 : A ; proj2 : P proj1 }.
Notation " { x : T & P } " := (sigma (fun x : T => P)).
Notation Π1 := proj1.
Notation Π2 := proj2.

Set Implicit Arguments.

(* end hide *)

(**

  This section presents our formalization of weak groupoids in %\Coq%
  with universe polymorphism.  We first explain our overloaded
  management of equalities and introduce type classes for weak
  groupoids and their associated structures, i.e., weak functors,
  natural transformations and homotopic equivalences
  (%\S\ref{sec:w2gpds}-\ref{sec:homequiv}%). Natural transformations
  give access to a homotopic form of functional extensionality, while
  homotopic equivalences provide extensionality at the level of types.
  Polymorphic universes are needed to state that weak groupoids and homotopic equivalences form a weak groupoid.
  Homotopic equivalences directly provides access to a rewriting mechanism
  on types (%\S\ref{sec:rew}%). This rewriting is used to extend functors 
  and products to dependent functors and dependent sums (%\S\ref{sec:depprod}-\ref{sec:sigma}%). 

 %\subsection{Notations} \input{notations}%

  
*)


(**

 ** Definition of weak groupoids
 %\label{sec:w2gpds}%
 We formalize weak groupoids using type classes.
 Contrarily to what is done in the setoid translation,
 the basic notion of morphisms is given as inhabitants of a relation in [Type]:

*)

Definition HomT (T : Type) := T -> T -> Type.

(**
  %\noindent%
  Homs are relations, that is inhabitants of type [HomT T] for a particular [T], 
  and morphisms are inhabitants of a hom.
  To manipulate hom-sets at rank 1 and 2 abstractly, we use ad-hoc 
  polymorphism and introduce type classes [HomT1] and [HomT2] with according notations. 

*)

Class HomT1 T := {eq1 : HomT T}.
Infix "~1" := ((_).(eq1)) (at level 80).

Class HomT2 {T} (Hom : HomT T) := 
  {eq2 : ∀ {x y : T}, HomT (Hom x y)}.
Infix "~2" := ((_).(eq2)) (at level 80).

(* begin hide *)
Infix "~" := (_.(eq2)) (at level 80). 
(* end hide *)

(** Given a [Hom], we define type classes that represent that the
  [Hom]-set of morphisms is reflexive (named [Identity], which
  corresponds to the identity morphism), symmetric (named [Inverse],
  which corresponds to the existence of an inverse morphism for every
  morphism, noted [f ^-1]) and transitive (named [Composition], which
  corresponds to morphisms composition, noted [g ° f]). Those three
  properties are gathered by the type class [Equivalence].
*)
(* begin hide *)

Class Identity {A} (Hom : HomT A) :=
  { identity : ∀ x, Hom x x }.

Class Inverse {A} (Hom : HomT A) :=
  { inverse : ∀ {x y:A}, Hom x y -> Hom y x }.

Class Composition {A} (Hom : HomT A) :=
  { composition : ∀ {x y z:A}, Hom x y -> Hom y z -> Hom x z }.

Notation  "g ° f" := (composition f g) (at level 50). 
Notation  "f ^-1" := (inverse f) (at level 45). 
Notation "[ T ]" := (proj1 T).
Notation " ( x ; p ) " := (@Build_sigma _ _ x p).
(* end hide *)

(* begin hide *)
Class Equivalence {T} (Eq : HomT T):= {
  Equivalence_Identity :> Identity Eq ;
  Equivalence_Inverse :> Inverse Eq ;
  Equivalence_Composition :> Composition Eq 
}.
(* end hide *)

(** We first define a [CategoryP] class where the structure of higher
  equalities is not specified.  
*)

Class CategoryP {T} {Hom1 : HomT1 T} (Hom2: HomT2 eq1) 
:= { Id :> Identity eq1; Comp :> Composition eq1;
     id_R : ∀ x y (f : x ~1 y), f ° identity x ~ f ;
     id_L : ∀ x y (f : x ~1 y), identity y ° f ~ f ;
     assoc : ∀ x y z w (f: x ~1 y) (g: y ~1 z) (h: z ~1 w),
              (h ° g) ° f ~ h ° (g ° f);
     comp : ∀ x y z (f f': x ~1 y) (g g': y ~1 z), 
              f ~ f' -> g ~ g' -> g ° f ~ g' ° f' }.

(**

  In a weak category, all 2-morphisms are invertible so the set of
  2-Homs denoted by [~2] corresponds to an equivalence relation. 
  Higher equalities are trivial, which can only be expressed by an axiom
  ([Trunc_2]).

*)


Class WeakCategory T := {
  Hom1 :> HomT1 T; Hom2 :> HomT2 eq1;
  Category_1 :> CategoryP Hom2;
  Equivalence_2 :> ∀ x y, (Equivalence (eq2 (x:=x) (y:=y))) }. 
Definition WeakCatType := {T:Type & WeakCategory T}.

(* begin hide *)

Hint Extern 1 (@Equivalence (@eq1 (@Hom1 ?T) ?x ?y) eq2) => 
  exact (@Equivalence_2 T x y) : typeclass_instances.
(* Hint Extern 1 (@CategoryP (proj1 ?T) (@Hom1 ?T) _) => exact (@Category_1 (proj2 T)) : typeclass_instances. *)
Hint Extern 1 (@HomT2 _ (@eq1 (@Hom1 ?T))) => exact (@Hom2 T) : typeclass_instances.
Hint Extern 1 (WeakCategory [?T]) => exact (proj2 T) : typeclass_instances.

(* end hide *)

(** 
    A weak groupoid is a weak category where all 1-Homs are invertible
    and subject to additional compatibility laws on the inversion. We define as
    [WeakGroupoidType] the type of [Type]s that have a weak groupoid structure.

*)

Class GroupoidP {T} {Hom1 : HomT1 T} {Hom2: HomT2 eq1} 
  (Cat : CategoryP Hom2) := { Inv :> Inverse eq1 ;
  inv_R : ∀ x y (f: x ~1 y), f ° f ^-1 ~ identity y ;
  inv_L : ∀ x y (f: x ~1 y), f ^-1 ° f ~ identity x ;
  inv :   ∀ x y (f f': x ~1 y), f ~ f' -> f ^-1 ~ f' ^-1}.

(* begin hide *)

Definition assoc' {T} {Hom1: HomT1 T} {Hom2: HomT2 eq1} {Category} {x y z w: T} :=
  assoc (CategoryP := Category) x y z w.

Definition id_L' {T} {Hom1: HomT1 T} {Hom2: HomT2 eq1} {Category} {x y: T} := 
  id_L (CategoryP := Category) x y .

Definition id_R' {T} {Hom1: HomT1 T} {Hom2: HomT2 eq1} {Category} {x y: T} := 
  id_R (CategoryP := Category) x y .

Definition HorComp {T} {Hom1 : HomT1 T} {Hom2: HomT2 eq1} 
           {Category_1 : CategoryP Hom2} {x y z} 
           {f f' : x ~1 y} {g g' : y ~1 z} : 
  f ~2 f' -> g ~2 g' -> g ° f ~2 g' ° f' := 
  comp _ _ _ f f' g g'.

Infix "**" := HorComp (at level 50).

(* end hide*)

Class WeakGroupoid T := {
  WC :> WeakCategory T ; G :> GroupoidP Category_1 }.

     (* is_Trunc_2 : ∀ (x y : T) *)
     (*             (e e' : x ~1 y) (E E' : e ~2 e'), E = E' }. *)


(* begin hide *)

Definition WeakGroupoidType := sigma WeakGroupoid.

Hint Extern 1 (WeakGroupoid [?T]) => exact (Π2 T) : typeclass_instances.

Axiom Trunc_2 : forall (T:WeakGroupoidType) (x y : [T])
  (e e' : x ~1 y) (E E' : e ~2 e'), E = E'.

(* Definition Trunc_2 (T:WeakGroupoidType) (x y : [T]) *)
(*   (e e' : x ~1 y) (E E' : e ~2 e') : E = E' := *)
(*   is_Trunc_2 x y e e' E E'. *)

(* Program Instance eq_pi1' (T : WeakGroupoidType) : WeakGroupoid [T] := Π2 T. *)

(* end hide *)


(* begin hide *)

Definition WeakGroupoidTypeToWeakCatType (T : WeakGroupoidType) : WeakCatType := 
  ([T] ; WC).

Coercion WeakGroupoidTypeToWeakCatType : WeakGroupoidType >-> WeakCatType. 

Lemma left_simplify_gen {T} {Hom1 : HomT1 T} {Hom2: HomT2 eq1} 
      (cat:CategoryP Hom2)
      (equiv : forall x y, Equivalence (eq2 (x:=x) (y:=y)))
      (x y z: T) (f f': x ~1 y) (g : y ~1 z) 
      (inv_g : z ~1 y) (inv_L : inv_g ° g ~2 identity y) : 
  g ° f ~ g ° f' -> f ~ f'.
Proof.
  intros Heq. assert ((inv_g ° g) ° f ~ (inv_g ° g) ° f').
  eapply composition. apply assoc.
  apply inverse; eapply composition. apply assoc. 
  apply inverse. apply comp. auto. apply identity. 
  eapply composition in X.  
  Focus 2.
  apply comp. apply identity. apply inverse, inv_L.
  eapply inverse in X.
  eapply composition in X.
  Focus 2.
  apply comp. apply identity. eapply inverse. apply inv_L. 
  eapply composition in X.
  Focus 2.
  eapply inverse;  apply id_L. apply inverse in X. eapply composition in X.
  Focus 2.
  eapply inverse;  apply id_L. auto.   
Qed.

Lemma right_simplify_gen {T} {Hom1 : HomT1 T} {Hom2: HomT2 eq1} 
      (cat:CategoryP Hom2)
      (equiv : forall x y, Equivalence (eq2 (x:=x) (y:=y)))
      (x y z: T) (f: x ~1 y) (g g' : y ~1 z) 
      (inv_f : y ~1 x) (inv_R : f ° inv_f ~2 identity y) : 
  g ° f ~ g' ° f -> g ~ g'.
Proof.
  intros Heq. assert (g ° (f ° inv_f) ~ g' ° (f ° inv_f)).
  eapply composition. eapply inverse. apply assoc.
  apply inverse; eapply composition. eapply inverse. apply assoc. 
  apply inverse. apply comp; auto. apply identity.
  eapply composition in X.
  Focus 2.
  apply comp; [idtac | apply identity]. eapply inverse. apply inv_R.
  eapply inverse in X.
  eapply composition in X.
  Focus 2.
  apply comp; [idtac | apply identity]. eapply inverse. apply inv_R. 
  eapply composition in X.
  Focus 2.
  eapply inverse;  apply id_R. apply inverse in X. eapply composition in X.
  Focus 2.
  eapply inverse;  apply id_R. auto.   
Defined.


Definition left_simplify (T:WeakCatType) (x y z: [T])
           (f f': x ~1 y) (g : y ~1 z) (inv_g : z ~1 y) 
           (inv_L : inv_g °g ~ identity y) :
  g ° f ~ g ° f' -> f ~ f' 
  := left_simplify_gen _ _ x y z f f' g inv_g inv_L.

Definition right_simplify (T:WeakCatType) (x y z: [T]) 
           (f: x ~1 y) (g g' : y ~1 z) (inv_f : y ~1 x) 
           (inv_R : f ° inv_f ~ identity y) : 
  g ° f ~ g' ° f -> g ~ g' 
  := right_simplify_gen _ _ x y z f g g' inv_f inv_R.

Lemma right_compose (T:WeakCatType) (x y z:[T]) (f: x ~1 y) (g g': y ~1 z) 
      (inv_f : y ~1 x) (inv_R : f ° inv_f ~2 identity y) 
      (inv_L : inv_f ° f ~2 identity x) :
  g ~2 g' -> g ° f ~2 g' ° f.
Proof.
  intro Heq. apply (right_simplify _ _ _ (inv_f) _ _ f inv_L).
  eapply composition. apply assoc.
  eapply inverse. eapply composition. apply assoc.
  eapply composition. apply comp; [idtac | apply identity].
  apply inv_R. eapply inverse. eapply composition. 
  apply comp; [idtac | apply identity]. apply inv_R. 
  eapply composition. apply id_R.
  eapply inverse. eapply composition. apply id_R.
  eapply inverse; auto.
Qed.

Lemma left_compose (T:WeakCatType) (x y z:[T]) (f f': x ~1 y) (g: y ~1 z) 
      (inv_g : z ~1 y) (inv_R : g ° inv_g ~ identity z) 
      (inv_L : inv_g ° g ~ identity y) : f ~ f' -> g ° f ~ g ° f'.
Proof.
  intro Heq. apply (left_simplify _ _ _ _ _ (inv_g) g inv_R).
  eapply composition. eapply inverse; apply assoc.
  eapply inverse. eapply composition. eapply inverse; apply assoc.
  eapply composition. apply comp. apply identity.
  apply inv_L. eapply inverse. eapply composition. apply comp.
  apply identity. apply inv_L. eapply composition. apply id_L.
  eapply inverse. eapply composition. apply id_L.
  eapply inverse; auto.
Qed.

Definition left_simplify' (T:WeakGroupoidType) (x y z: [T]) (f f': x ~1 y) 
           (g : y ~1 z) : g ° f ~ g ° f' -> f ~ f' := 
  left_simplify (T:=T) x y z f f' g (inverse g) (inv_L _ _ _).

Definition right_simplify' (T:WeakGroupoidType) (x y z: [T]) (f : x ~1 y)
           (g g' : y ~1 z)
  := right_simplify (T:=T) x y z f g g' (inverse f) (inv_R _ _ _).

Definition left_compose' (T:WeakGroupoidType) (x y z:[T]) (f f': x ~1 y) 
           (g: y ~1 z) 
  := left_compose (T:=T) x y z f f' g (inverse g) (inv_R _ _ _ ) (inv_L _ _ _ ). 

Definition right_compose' (T:WeakGroupoidType) (x y z:[T]) (f : x ~1 y) 
           (g g': y ~1 z)
  := right_compose (T:=T) x y z f g g' (inverse f) (inv_R _ _ _) (inv_L _ _ _).

Lemma comp_inv (T:WeakGroupoidType) (x y z:[T]) (f : x ~1 y) (g : y ~1 z) : 
  inverse f ° inverse g ~ inverse (g ° f).
Proof.
  apply (left_simplify' _ _ _ _ _ (g°f)).
  eapply inverse. eapply composition; try apply inv_R.
  eapply inverse. eapply composition. 
  Focus 2.
  apply inv_R.
  eapply composition. apply assoc.
  apply left_compose'. 
  eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity.
  apply inv_R.
  eapply composition. apply id_L.
  apply identity.
 Qed.

Lemma inv_inv (T:WeakGroupoidType) (x y:[T]) (e : x ~1 y) : 
  inverse (inverse e) ~ e.
Proof.
  apply (left_simplify' _ _ _ _ _ (inverse e)).
  eapply composition. apply inv_R. eapply inverse. apply inv_L. 
Defined.

Lemma inv_id (T:WeakGroupoidType) (x:[T]) : 
  inverse (identity x) ~ identity x.
Proof.
  eapply inverse. eapply composition; [idtac | apply id_L]. 
  eapply inverse. apply inv_R. 
Qed.

Lemma comp_id (T:WeakGroupoidType) (x:[T]) : 
  identity x ° identity x ~ identity x.
Proof.
  eapply composition; try apply id_L. apply identity.
Qed.

(* end hide *)


(** 

** Weak Functors and natural transformations

%\label{sec:funextnat}%

A morphism between two weak groupoids is a weak functor, i.e., a function
between objects of the weak groupoids that transports homs and
subject to compatibility laws. 
**)

Class WeakFunctor {T U : WeakGroupoidType} (f : [T] -> [U]) : Type :=
{ _map : ∀ {x y}, x ~1 y -> f x ~1 f y ;
  _map_comp : ∀ {x y z} (e:x ~1 y) (e':y ~1 z),
                _map (e' ° e) ~2 _map e' ° _map e ;
  _map2 : ∀ {x y:[T]} {e e' : x ~1 y},
          (e ~2 e') -> _map  e ~2 _map e' }.

Definition Fun_Type (T U : WeakGroupoidType) :=
  sigma (@WeakFunctor T U).

(* begin hide *)

Infix "--->" := Fun_Type (at level 55). 

Notation "'map' f" := ((proj2 f).(_map)) (at level 0, f at level 0).
Notation map_comp f := ((proj2 f).(_map_comp)).
Notation map2 f := ((proj2 f).(_map2)).

Hint Extern 0 (WeakFunctor [?f]) => exact (proj2 f) : typeclass_instances.

(* end hide *)
(** 

%\noindent%
We note [T ---> U] the type of weak functors from [T] to [U].
Note that we only impose compatibility with the composition as
compatibilities with identities and inverse Homs can be deduced
from it. The following notation defines application for a function that 
is a dependent pair of a computation and of properties on that computation.


*)

Notation "M @ N" := ([M] N) (at level 55). 

(* begin hide *)

Lemma map_id {T U} (f : T ---> U) {x} :
  map f (identity x) ~ identity (f @ x).
Proof.
  apply (right_simplify' _ _ _ (map f (identity x))).
  eapply composition. eapply inverse, (map_comp f).
  eapply composition. eapply (map2 f). apply id_L. eapply inverse. apply id_L. 
Defined.

Lemma map_inv {T U} (f : T ---> U) :
  ∀ x y (e : x ~1 y) , map f (inverse e) ~ inverse (map f e).
Proof.
  intros. eapply right_simplify'.
  eapply composition. eapply inverse, (map_comp f).
  eapply composition. eapply (map2 f). apply inv_L.
  eapply composition. apply (map_id f). eapply inverse. apply inv_L.
Defined.

Opaque map_id map_inv.

Program Instance arrow_id (T:WeakGroupoidType) : WeakFunctor (id (A := [T])) :=
  { _map x y e := e ;
    _map_comp x y z e e' := identity _ }.

Program Instance id_fun : Identity Fun_Type :=
  { identity x := (id (A:=[x]) ; arrow_id _) }.

Program Instance arrow_comp A B C (f : A ---> B) (g : B ---> C) : 
  WeakFunctor (λ x : [A], g @ (f @ x)) :=
  { _map x y e := map g (map f e) }.
Next Obligation. 
Proof.
  eapply composition.
  eapply (map2 g). apply (map_comp f e e'). eapply (map_comp g). 
Defined.
Next Obligation. apply (map2 g). apply (map2 f). auto. Defined.
 
Program Instance comp_fun : Composition Fun_Type :=
  { composition x y z X X0 := (λ x, X0 @ (X @ x) ; _) }.

(* end hide *)

(**

  Equivalence between functors is given by (iso-)natural transformations.
  We insist here that this naturality condition in the 
  definition of functional extensionality is crucial in a higher setting. 
  It is usually omitted in formalizations of homotopy theory in Coq because
  there they only consider the 1-groupoid case where
  the naturality becomes trivial, see for instance%~\cite{coq_unival_axiom}%. 

*)

Class NaturalTransformation T U {f g : T ---> U} 
      (α : ∀ t : [T], f @ t ~1 g @ t) := 
  {_α_map : ∀ {t t'} (e : t ~1 t'), 
      α t' ° map f e ~ map g e ° α t}.

Definition nat_trans T U (f g : T ---> U) :=
  {α : ∀ t : [T], f @ t ~1 g @ t & NaturalTransformation α}.

(* begin hide *)

Hint Extern 0 (NaturalTransformation [?f]) => exact (proj2 f) : typeclass_instances.

Notation α_map f := ((proj2 f).(_α_map)).
 
Instance nat_transHom T U : HomT1 (T ---> U) := {eq1 := nat_trans (T:=T) (U:=U)}.

(* end hide *)

Definition modification T U (f g : T ---> U) 
 (α β : nat_trans f g) := ∀ t : [T], α @ t ~ β @ t.

(* begin hide *)

Instance modificationHom T U : HomT2 eq1 := {eq2 := modification (T:=T) (U:=U)}.

Program Instance _nat_id T U (f : T ---> U) : 
  NaturalTransformation (λ t : [T], identity (f @ t)).
Next Obligation. 
Proof.
  intros. eapply composition. apply id_L.
  eapply inverse. apply id_R. 
Defined.

Program Instance nat_id T U : Identity (nat_trans (T:=T) (U := U)).
Next Obligation. 
  rename x into f. 
  exact (λ t, identity (f @ t); _nat_id _ _ f). 
Defined.

Program Instance _nat_inv T U (f g : T ---> U) (H : nat_trans f g) :
  NaturalTransformation (λ t : [T], inverse  (H @ t)).
Next Obligation. intros. simpl in *. 
  eapply (left_simplify (T:=U)).
  apply inv_L.
  eapply composition. eapply inverse; apply assoc.
  eapply composition. apply comp. apply identity.
  apply inv_R. eapply inverse.
  eapply composition. eapply inverse; apply assoc. 
  eapply composition. apply comp. apply identity.
  apply (α_map H). eapply composition. apply assoc.
  eapply composition. apply comp. apply inv_R.
  apply identity.
  eapply composition. apply id_R.
  eapply composition. apply identity. eapply inverse. apply id_L.
Defined.

Program Instance nat_inv T U : Inverse (nat_trans (T:=T) (U := U)).
Next Obligation. rename x into f, y into g, X into H. 
       exact (λ t , inverse (H @ t); _nat_inv T U f g H). Defined.
  
Program Instance _nat_comp T U (f g h : T ---> U) (H : nat_trans f g) 
        (H' : nat_trans g h) : 
  NaturalTransformation (λ t : [T], (H' @ t) ° (H @ t)).

Next Obligation. 
Proof.
  intros. eapply composition. apply assoc.
  eapply composition. apply comp. apply (α_map H). apply identity.
  eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity. apply (α_map H').
  eapply composition. apply assoc. apply identity. 
Defined.

Program Instance nat_comp T U : Composition (nat_trans (T:=T) (U := U)).

Next Obligation. 
Proof.
  rename x into f, y into g, z into h,X into H, X0 into H'. 
  exact (λ t , composition (H @ t) (H' @ t); _nat_comp T U f g h H H').
Defined.

Program Instance nat2_id T U (f g : T ---> U) : 
  Identity (modification (f:=f) (g:=g)).
Next Obligation. exact (λ t, identity _). Defined.

Program Instance nat2_inv T U (f g : T ---> U) : 
  Inverse (modification (f:=f) (g:=g)).
Next Obligation. rename X into E. exact (λ t, inverse (E t)). Defined.

Program Instance nat2_comp T U (f g : T ---> U) :
  Composition (modification (f:=f) (g:=g)).
Next Obligation. rename X into E, X0 into  F. exact (λ t, (F t) ° (E t)). Defined.

Program Instance nat_trans_cat T U : CategoryP (modificationHom T U).
Next Obligation. intro t. apply id_R. Defined.
Next Obligation. intro t. apply id_L. Defined.
Next Obligation. intro t. apply assoc. Defined.
Next Obligation. intro t. apply comp. apply X. apply X0 . Defined.

Program Instance nat_trans_grp T U : GroupoidP (nat_trans_cat T U).
Next Obligation. intro t. apply inv_R. Defined.
Next Obligation. intro t. apply inv_L. Defined.
Next Obligation. intro t. apply inv, X. Defined.

Program Instance modification_eq T U (f g : T ---> U) : 
  Equivalence (modification (f:=f) (g:=g)).

Program Instance nat_category T U : WeakCategory (T ---> U) := 
  {| Hom1 := nat_transHom T U; Hom2 := modificationHom T U|}.

Program Instance nat_groupoid (T U : WeakGroupoidType) : WeakGroupoid (T ---> U).
(* Next Obligation.  *)
(*   intros. red in E, E'. red in e, e'. destruct e as [f Hf], e' as [f' Hf'].  *)
(*   simpl in E. simpl in *.  *)
(*   apply (@Trunc_2 U ([x] z) ([y] z) (f z) (f' z) (E z) (E' z)).  *)
(* Qed. *)


(* end hide *)

(** %\noindent%
    We can now equip the functor space with a weak groupoid structure. Note
    here that we (abusively) use the same notation for the functor type and 
    its corresponding weak groupoid. *)

(* begin hide *)

(*
 In the definition above, [_] is instantiated by a proof that [nat_trans] and [modification] form a weak groupoid on [T ---> U]. 
 *)

Definition _fun T U : WeakGroupoidType := 
  (T ---> U ; nat_groupoid _ _). 

Infix "-->" := _fun (at level 90). 

(* end hide *)

(* begin hide *)

Instance FunTypeHom : HomT1 WeakGroupoidType := {eq1 := Fun_Type}.

Instance nat_transHom' : HomT2 Fun_Type := {eq2 := nat_trans}.

Program Instance category_fun : CategoryP nat_transHom'. 

Next Obligation. 
Proof. 
  exists (λ t , identity _). econstructor. intros. simpl.
  eapply composition. apply id_L. eapply inverse. apply id_R.
Defined.
Next Obligation. 
Proof.
  exists (λ t , identity _). econstructor. intros. 
  eapply composition. apply id_L. eapply inverse. apply id_R. 
Defined.
Next Obligation.
Proof.
  exists (λ t , identity _).  econstructor. intros. 
  eapply composition. apply id_L. eapply inverse. apply id_R. 
Defined.
Next Obligation. 
Proof.
  exists (λ t , map g' (X @ t) ° (X0 @ (f @ t))). econstructor. intros. 
  eapply composition. apply assoc.
  eapply composition. apply comp. apply (α_map X0). apply identity.
  eapply composition. eapply inverse. apply assoc. eapply inverse.
  eapply composition. eapply inverse. apply assoc. 
  apply comp. apply identity. eapply composition.
  Focus 2. eapply composition. Focus 2. apply (map_comp g').  
  eapply (map2 g'). eapply inverse. apply (α_map X).
  eapply inverse. simpl. apply (map_comp g'). 
Defined.

Program Instance _eq : ∀ (T U : WeakGroupoidType), 
                         Equivalence (nat_trans (T:=T) (U:=U)).
 
Instance WeakCategory_fun : WeakCategory WeakGroupoidType | 2 :=
  {| Hom1 := FunTypeHom; Hom2 := nat_transHom' |}.

Definition nat_id_R  := (category_fun.(id_R)).
Definition nat_id_L  := category_fun.(id_L).
Definition nat_assoc := category_fun.(assoc).
Definition nat_comp'  := category_fun.(comp).

Lemma nat_comp2 A B C (f f': A ~1 B) (g g' : B ~1 C) 
      (H H': f ~1 f') (G G' : g ~1 g') (e: H ~2 H') (e':G ~2 G') :
    nat_comp' H G ~ nat_comp' H' G'.
Proof.
  intro a. simpl. apply comp. apply e'. apply (map2 g' (e a)).
Defined.

Lemma nat_comp_id A B C (f : A ---> B) (g : B ---> C) :
    nat_comp' (identity f) (identity g) ~ identity _.
Proof.
  intro a. simpl in *. eapply composition. apply id_R. apply (map_id g).
Defined.

(* Tactics for simplification of goals containing [identity] applications. *)

Ltac simpl_id_end' := eapply composition ; [match goal with
                   | [ |- eq2 (?P ^-1 ° ?P) _] => 
                     apply inv_L
                   | [ |- eq2 (?P ° ?P ^-1) _] => 
                     apply inv_R
                   | [ |- eq2 (?P ° identity ?x) _] => 
                     apply id_R
                   | [ |- eq2 (identity ?x ° ?P) _] => 
                     apply id_L
                   | [ |- eq2 ((?P ^-1)^-1) _] => 
                     apply inv_inv
                   | [ |- eq2 (inverse (identity _)) _] => 
                     apply inv_id
                 end | idtac].

Ltac simpl_id_end_extended' := first [ simpl_id_end' |
                                      match goal with
                   | [ |- eq2 ?e _ ] => apply (identity e)
                   | [ |- _ ] => idtac
                 end].

Ltac simpl_id' := first [simpl_id_end' ; simpl_id' |
                        match goal with
                   | [ |- eq2 (?P ^-1) _] => eapply composition;
                              [apply inv ; simpl_id' | idtac]; 
                              try apply identity
                   | [ |- eq2 (map ?F (identity _)) _] => eapply composition;
                              [eapply (map_id F); simpl_id' | idtac]; 
                              simpl_id'
                   | [ |- eq2 (map ?F ?P) _] => first [
                          eapply composition;
                              [eapply (map2 F); simpl_id' | idtac]; 
                              [apply identity | idtac] | 
                          (progress_evars (eapply composition;
                              [eapply (@_map2 _); simpl_id' | idtac]; instantiate)) ; simpl_id' |
                          idtac]
                   | [ |- eq2 (?Q ° ?P) _] => eapply composition;
                                             [apply comp; simpl_id' | idtac];
                                            simpl_id_end_extended'
                   | [ |- eq2 ?e _ ] => first [has_evar e; idtac | apply (identity e)]
                   | [ |- _ ] => idtac
                 end].

Ltac simpl_id_bi' := simpl_id'; eapply inverse; simpl_id'.

(* end hide *)

(** 
 ** Homotopic equivalences
 %\label{sec:homequiv}%   

    The standard notion of equivalence between weak groupoids is given by
    adjoint equivalences, that is a map with an [adjoint] and two proofs
    that they form a [section] (or counit of the adjunction) and a
    [retraction] (or unit of the adjunction). *)

Class Iso_struct T U (f : [T --> U]) := 
{ _adjoint :    [U --> T] ;
  _section :    f ° _adjoint ~ identity U ;
  _retraction : _adjoint ° f ~ identity T}.

(* begin hide *)

Definition Iso A B := {f : A ---> B & Iso_struct f}.

(* Notations for [Iso] projections. *)

Notation adjoint' f := f.(proj2).(_adjoint).
Notation section' f := f.(proj2).(_section).
Notation retraction' f := f.(proj2).(_retraction).

(* end hide *)

(** This type class defines usual equivalences. To get an adjoint
    equivalence, an additional triangle identity between sections and
    retractions is required. This allows to eliminate a section against
    a retraction in proofs. A corresponding triangle identity involving
    [adjoint f] can also be expressed, but it can be shown that each
    condition implies the other.  *)

Class Equiv_struct T U (f : T ---> U) := 
{ iso : Iso_struct f;
  _triangle : ∀ t, (_section @ (f @ t)) ~ map f (_retraction @ t)}.

Definition Equiv A B := {f : A ---> B & Equiv_struct f}.

(* begin hide *)

Infix "<~>" := Equiv (at level 55). 

Hint Extern 0 (Equiv_struct [?f]) => exact (proj2 f) : typeclass_instances.
Hint Extern 0 (Iso_struct [?f]) => exact (@iso (proj2 f)) : typeclass_instances.

(* Notations for [Equiv] projections. *)
Notation adjoint f := f.(proj2).(iso).(_adjoint).
Notation section f := f.(proj2).(iso).(_section).
Notation retraction f := f.(proj2).(iso).(_retraction).
Notation triangle f := f.(proj2).(_triangle).

Program Definition map_trans A B (f : [A --> B]) : f ~1 f :=
  ((fun t => map f (identity t)); _).

Next Obligation.
Proof.
  econstructor. intros. simpl.
  eapply composition. eapply composition. apply comp. apply identity.
  apply map_id. apply id_L. apply inverse.
  eapply composition. apply comp. apply map_id. apply identity. apply id_R.
Defined.

Program Instance EquivToIso_ A B (f : A <~> B) : Iso_struct [f].
Next Obligation. exact (adjoint f). Defined.
Next Obligation. exact (section f). Defined.
Next Obligation. exact (retraction f). Defined.

Definition EquivToIso A B (f : A <~> B) := ([f]; EquivToIso_ _ _ f).

Lemma Equiv_map_injective {A B} (f: Iso A B) {x y : [A]} (e e': x ~1 y) :
  map [f] e ~ map [f] e' -> e ~ e'.
Proof.
  intros H. apply (map2 (adjoint' f)) in H.
  eapply left_compose' in H.
  eapply composition in  H. Focus 2. eapply inverse. apply (α_map (retraction' f)).
  apply inverse in H.
  eapply composition in  H. Focus 2. eapply inverse. apply (α_map (retraction' f)).
  apply right_simplify' in H. exact (inverse H).
Defined.

Program Instance _Iso_inv {A B} (f : Iso A B) : Iso_struct (adjoint' f).
Next Obligation. exact [f]. Defined.
Next Obligation. exact (retraction' f). Defined.
Next Obligation. exact (section' f). Defined.

Instance _Type_iso_inv : Inverse Iso := 
  { inverse T U f := (adjoint' f ; _Iso_inv f) }.

Lemma nat_on_id A (f : [A --> A]) (α : f ~ identity _) (a:[A]) : 
  α @ (f @ a) ~ map f (α @ a).
Proof.
  eapply left_simplify'. apply inverse. apply (α_map α).
Defined.

Definition triangle' A B (f : A <~> B) : 
  forall u, map (adjoint f) (section f @ u) ~ (retraction f @ _).
Proof.
  intros.
  assert (triangle := triangle f (adjoint f @ u)).
  assert (foo := α_map (section f) (section f @ u)). simpl in foo.
  apply (map2 (adjoint f)) in foo. 
  eapply composition in foo. Focus 2.
  eapply inverse. apply _map_comp. 
  eapply inverse in foo. eapply composition in foo. Focus 2.
  eapply inverse. apply _map_comp. 
  eapply composition in foo. Focus 2. apply comp. 
  eapply inverse. apply (map2 (adjoint f) triangle). apply identity.
  eapply composition in foo. Focus 2. apply comp. 
  apply (nat_on_id (retraction f)). apply identity.
  eapply composition in foo. Focus 2. 
  apply (α_map (retraction f) (map (adjoint f) (section f @ u))). 
  eapply right_simplify'. eapply inverse. apply foo.
Defined.

Program Instance IsoToEquiv'' A B (f : Iso A B) : Iso_struct [f].
Next Obligation. exact (adjoint' f). Defined.
Next Obligation. 
  pose (F := (map_trans (adjoint' f)) ** retraction' f ** map_trans [f]).
  pose (idL := id_L _ _ (adjoint' f)).
  pose (idLf := idL ** map_trans [f]).
  pose (G := map_trans (adjoint' f) ** map_trans [f] ** section' f).
  pose (ass := assoc _ _ _ _ (adjoint' f) [f] (adjoint' f) ** map_trans [f]).
  pose (idR := id_L _ _ ([f] °adjoint' f)).
  pose (idRf := inverse idR).
  pose (ass' := assoc _ _ _ _ ([f] ° adjoint' f) (adjoint' f) [f]).
  exact (section' f ° idLf ° F ° inverse ass ° ass' ° inverse G ° idRf).
Defined.
Next Obligation. exact (retraction' f). Defined.

Definition IsoToEquiv' A B (f : Iso A B) := ([f] ; IsoToEquiv'' _ _ f).

Program Instance IsoToEquiv_ A B (f : Iso A B) : Equiv_struct [f].
Next Obligation. simpl_id'. simpl_id'.
  unfold IsoToEquiv''_obligation_3.
  eapply right_simplify'. eapply composition. apply assoc.
  eapply composition. apply comp. apply inv_L. apply identity.
  simpl_id'. eapply composition. apply comp.
  apply (map2 [f] (nat_on_id (retraction' f) t)). apply identity.
  apply (α_map (section' f)).
Defined.

(* end hide *)

(** 

   It is well known that any equivalence can be turned into an adjoint
   equivalence by slighty modifying the section. While available in
   our formalization, this result should be used with care has it
   opacifies the underlying notion of homotopy and can harden later
   proofs.

*)

Definition IsoToEquiv A B (f : Iso A B) : Equiv A B.
Proof. exact ([f]; IsoToEquiv_ _ _ f). Defined.

(* begin hide *)

(** Definition of identity homotopic equivalence *)

Program Instance __Equiv_Id {T} : Iso_struct (identity T).
Next Obligation. exact (identity T). Defined.
Next Obligation. 
Proof.
  exists (λ t , identity t). econstructor. intros.
  refine ((_nat_id T T (identity T)).(_α_map) _). 
Defined.
Next Obligation. 
Proof. 
  exists (λ t , identity t). econstructor. intros.
  refine ((_nat_id T T (identity T)).(_α_map) _). 
Defined.

Program Instance _Equiv_Id {T} : Equiv_struct (identity T).
Next Obligation. apply identity. Defined.

Instance _Type_id : Identity Equiv := { identity T := (identity T ; _Equiv_Id) }.

(** Definition of inverse of homotopic equivalence **)

Program Instance __Equiv_inv {A B} (f : A <~> B) : Iso_struct (adjoint f).
Next Obligation. exact [f]. Defined.
Next Obligation. exact (retraction f). Defined.
Next Obligation. exact (section f). Defined.

Program Instance _Equiv_inv {A B} (f : A <~> B) : Equiv_struct (adjoint f).
Next Obligation. apply inverse. apply (triangle' f _). Defined.

Instance _Type_inv : Inverse Equiv := 
  { inverse T U f := (adjoint f ; _Equiv_inv f) }.

Instance Adjoint_WeakFunctor T U (f : T <~> U) : WeakFunctor [adjoint f] :=
  Π2 (adjoint f).
  
Program Instance __Equiv_comp {A B C} (f : A <~> B) (g : B <~> C) : 
  Iso_struct ([g] ° [f]).
Next Obligation. exact (adjoint f ° adjoint g). Defined.

Obligation Tactic := intros.

Next Obligation. 
Proof. eapply composition. apply nat_assoc. 
  eapply composition. apply nat_comp'. eapply composition. 
  eapply inverse, nat_assoc.
  eapply composition. apply nat_comp'. apply identity. apply (section f).
  apply nat_id_L. apply identity. apply (section g).
Defined.
Next Obligation. 
  eapply composition. apply nat_assoc.
  eapply composition. apply nat_comp'. eapply composition. 
  eapply inverse, nat_assoc.
  eapply composition. apply nat_comp'. apply identity. eapply (retraction g).
  apply nat_id_L. apply identity. eapply (retraction f). 
Defined.

Program Instance _Equiv_comp {A B C} (f : A <~> B) (g : B <~> C) : 
  Equiv_struct ([g] ° [f]).

Next Obligation. 
Proof.
  simpl. simpl_id_bi'.
  apply inverse. eapply composition.
  apply comp. apply identity. apply (triangle g).
  eapply composition. eapply inverse. apply _map_comp. apply (map2 [g]).
  eapply composition. eapply inverse. apply (α_map (section f)).
  eapply composition. apply comp. apply identity. apply (triangle f). 
  eapply inverse. apply (map_comp [f]). 
Defined.

Instance _Type_comp : Composition Equiv := 
  { composition T U V f g := ([g] ° [f] ; _Equiv_comp f g) }.

(* end hide *)
(** 

  Weak groupoids and homotopic equivalences between them form a weak
  2-groupoid.  Equality of homotopic equivalences is given by
  equivalence of adjunctions.  As we only consider weak groupoids, the
  last level of equality is lost in the axiom [Trunc_2].

*)



(** Two adjunctions are equivalent if their left adjoint are
  equivalent and they agree on their sections (up-to the isomorphism).
  Note that equivalence of the right adjoint and agreement on their
  retractions can be deduced and so are not part of the definition.  *)

(* begin hide *)

Definition Equiv_adjoint A B (f f': Equiv A B) : 
  [f] ~1 [f'] -> adjoint f ~1 adjoint f'.
Proof.
  intro.
  eapply composition. apply inverse, id_L.
  eapply composition. apply nat_comp'. apply identity. 
  apply (inverse (retraction f')). eapply composition. apply nat_assoc. 
  eapply composition. apply nat_comp'. 
  eapply composition. apply nat_comp'. apply identity. apply (inverse X).
  apply (section f). apply identity. apply nat_id_R.
Defined.

Lemma Equiv_injective A B (f: A <~> B) x y : [f] @ x ~1 [f] @ y -> x ~1 y.
Proof.
  intros e. 
  eapply composition. pose (inverse (retraction f)). apply [n].
  eapply inverse. eapply composition; pose (inverse (retraction f)). apply [n].
  apply (map (adjoint f) (inverse e)).
Defined.

Definition Equiv_adjoint_simpl A B (f f': A <~> B) (H: [f] ~1 [f']) a :
  [Equiv_adjoint H] a ~ 
     map (adjoint f') ([section f] a ° inverse ([H] ([adjoint f] a)))
   ° [inverse (retraction f')] ([adjoint f] a).
Proof.
  unfold Equiv_adjoint. simpl. simpl_id'. apply identity.
Defined.

Opaque Equiv_adjoint.

Lemma triangle_inv' A B (f : A <~> B) : forall u, 
  map (adjoint f) (section f @ u) ° inverse (retraction f @ _) ~ identity _.
Proof.
  intro. eapply composition. apply comp. apply identity. 
  apply (triangle' f). apply inv_R.
Defined.

Lemma triangle_inv A B (f : A <~> B) : ∀ t, 
  (section f @ ([f] @ t)) ° map [f] ((inverse (retraction f)) @ t) ~ identity _.
Proof.
  intro. eapply composition. apply comp. apply identity. apply (triangle f). 
  eapply composition. apply comp. apply map_inv. apply identity. apply inv_R.
Defined.

Lemma Equiv_adjoint_id A B (f : A <~> B) :
 modification (Equiv_adjoint (identity [f])) (identity _).
Proof.
  intro b. eapply composition. apply Equiv_adjoint_simpl.
  eapply composition. apply comp. apply identity. eapply composition. eapply (map2 (adjoint f)).
  eapply composition. apply comp. apply inv_id. apply identity. apply id_R.
  apply identity. apply (triangle_inv' f).
Defined.

Lemma Equiv_adjoint2 A B (f g: A <~> B) (H H': [f] ~1 [g] ) (e : H~ H'):
 Equiv_adjoint H ~ Equiv_adjoint H'.
Proof.
  intro b. eapply composition. apply Equiv_adjoint_simpl.
  eapply inverse.  eapply composition. apply Equiv_adjoint_simpl.
  apply comp; try apply identity. apply (map2 (adjoint g)).
  apply comp; try apply identity. apply inv. eapply inverse, e.
Defined.  

Lemma Equiv_adjoint_inv A B (f g: A <~> B) (H : [f] ~1 [g] ) :
 Equiv_adjoint H ° Equiv_adjoint (inverse H) ~ identity _.
Proof.
  intro b. eapply composition. apply comp; apply Equiv_adjoint_simpl.
  eapply composition. apply assoc. eapply composition. apply comp.
  apply (α_map ((inverse (retraction g)) : nat_trans _ _)). 
  apply (map_comp (adjoint g)).
  eapply composition. apply assoc. eapply composition. apply comp.
  eapply composition. eapply inverse; apply assoc. eapply composition. 
  apply comp. apply identity. eapply composition. 
  eapply inverse, (map_comp (adjoint g)). eapply composition.
  eapply (map2 (adjoint g)).
  assert (foo := Π2 (inverse H)). apply foo.
  apply (map_comp (adjoint g)). apply identity. apply identity.
  eapply composition. eapply inverse; apply assoc. eapply composition. 
  apply comp. apply identity.
  eapply composition. eapply inverse; apply assoc. eapply composition. 
  apply comp. apply identity.
  eapply composition. eapply inverse, (map_comp (adjoint g)). eapply composition.
  eapply (map2 (adjoint g)). eapply composition. apply comp.
  apply (map_comp [f]). apply identity.
  eapply composition. eapply inverse; apply assoc. eapply composition. 
  apply comp. apply identity.
  apply (α_map (section f)). simpl. 
  eapply composition. apply assoc. eapply composition.
  apply comp. apply (triangle_inv f). apply identity. apply id_R. 
  apply (map_comp (adjoint g)).
  eapply composition. apply assoc. eapply composition. apply comp.
  eapply composition. eapply inverse, (map_comp (adjoint g)). eapply composition.
  eapply (map2 (adjoint g)). apply inv_L. apply (map_id (adjoint g)). 
  apply identity. apply id_R. apply (triangle_inv' g).
Defined.

Lemma Equiv_adjoint_comp A B (f f' f'': A <~> B) (H : [f] ~1 [f']) (H' : [f'] ~1 [f'']):
 Equiv_adjoint (H' ° H) ~ Equiv_adjoint H' ° Equiv_adjoint  H.
Proof.
  intro b. eapply composition. apply Equiv_adjoint_simpl.
  eapply composition. apply comp. apply identity.  eapply composition. 
  eapply (map2 (adjoint f'')).
  apply comp. eapply inverse, comp_inv. apply identity.
  eapply composition. apply (map_comp (adjoint f'')). apply comp.
  apply (map_comp (adjoint f'')). apply identity.
  eapply inverse. eapply composition. apply comp; apply Equiv_adjoint_simpl.
  eapply composition. apply assoc. eapply composition. apply comp.
  apply (α_map (inverse (retraction f'') : nat_trans _ _)). 
  apply (map_comp (adjoint f'')).
  eapply composition. apply assoc. eapply composition. apply comp.
  eapply composition. eapply inverse; apply assoc. eapply composition. 
  apply comp. apply identity.
  eapply composition. eapply inverse, (map_comp (adjoint f'')). 
  eapply composition. eapply (map2 (adjoint f'')).
  assert (foo := Π2 (inverse H')). apply foo.
  apply (map_comp (adjoint f'')). apply identity. apply identity.
  eapply composition. eapply inverse; apply assoc. eapply composition. 
  apply comp. apply identity.
  eapply composition. eapply inverse; apply assoc. eapply composition. 
  apply comp. apply identity.
  eapply composition. eapply inverse, (map_comp (adjoint f'')). 
  eapply composition. eapply (map2 (adjoint f'')). 
  eapply composition. apply comp.
  apply (map_comp [f']). apply identity.
  eapply composition. eapply inverse; apply assoc. eapply composition. 
  apply comp. apply identity.
  apply (α_map (section f')). simpl. 
  eapply composition. apply assoc. eapply composition.
  apply comp. apply (triangle_inv f'). apply identity.
  apply id_R. apply (map_comp (adjoint f'')).
  eapply composition. apply assoc. eapply composition. apply comp.
  eapply composition. eapply inverse, (map_comp (adjoint f'')). 
  eapply composition. eapply (map_comp (adjoint f'')). 
  apply identity. apply identity. apply identity. apply identity.
Defined.

(* end hide *)

Class EquivEq T U (f g : Equiv T U) (α : [f] ~ [g]) : Type :=  
{ _eq_section : 
    section f ~ section g ° (nat_comp' (Equiv_adjoint α) α) }. 

Definition Equiv_eq T U (f g : Equiv T U) := 
  {α : nat_trans [f] [g] & EquivEq α}.

(* begin hide *)

Instance equiveq_pi T U (f g : T <~> U) (α:Equiv_eq f g) : EquivEq [α] := Π2 α.

Notation eq_section α := α.(proj2).(_eq_section).

Definition eq_retraction {T U} {f g : T <~> U} (α:Equiv_eq f g) : 
  retraction f ~
  retraction g ° (nat_comp' [α] (Equiv_adjoint [α])).
Proof.
  intro. apply (Equiv_map_injective (EquivToIso f)). simpl.
  eapply composition. eapply inverse. apply (triangle f).
  eapply composition. apply (eq_section α). simpl. apply inverse.
  eapply composition. apply _map_comp.
  eapply left_simplify'. eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity.
  apply (α_map [α]). unfold id. 
  eapply composition. apply assoc. eapply composition. apply comp. apply identity.
  eapply inverse. apply (triangle g). apply inverse.
  eapply composition. apply comp. apply comp. eapply inverse. apply (α_map [α]).
  apply identity. apply identity. 
  eapply composition. eapply inverse. apply assoc. 
  eapply composition. apply comp. apply identity.
  eapply inverse. apply (α_map (section g)). eapply composition. apply assoc.
  apply comp; [idtac | apply identity].
  eapply composition. eapply inverse. apply assoc. apply inverse.
  eapply composition. apply comp. apply _map_comp. apply identity.
  eapply composition. eapply inverse. apply assoc.
  apply comp; [apply identity | idtac]. apply (α_map [α]).
Defined.

Axiom AllEquivEq : forall T U (f g : T <~> U) (α : nat_trans [f] [g]),
                     EquivEq α.

Lemma ExLawComp_nat A B C (f f' f'': A ~1 B) (g g' g'' : B ~1 C) 
      (H:f ~1 f') (H': f' ~1 f'') (G : g ~1 g') (G': g' ~1 g'') :
    nat_comp' (H' ° H) (G' ° G) ~2 nat_comp' H' G' ° nat_comp' H G.
Proof.
  intro a. simpl. eapply composition. 
  apply comp. apply identity. apply (map_comp g''). 
  eapply composition. apply assoc. eapply inverse.
  eapply composition. apply assoc. apply comp; try apply identity. 
  eapply composition. eapply inverse. apply assoc. 
  eapply composition. apply comp. apply identity.
  apply (Π2 G'). eapply composition. apply assoc. apply identity.
Defined.

Program Instance Id_Equiv_eq T U : Identity (Equiv_eq (T:=T) (U:=U)).
Next Obligation. 
Proof.
  exists (identity [x]).
  econstructor. 
  intro u. eapply composition. eapply inverse. apply id_R.
  apply comp; try apply identity. eapply inverse. 
  eapply composition. 
  eapply (nat_comp2 (Equiv_adjoint_id _) (identity _) u). 
  apply (nat_comp_id _ _ u).
Defined.                 

Program Instance Inv_Equiv_eq T U : Inverse (Equiv_eq (T:=T) (U:=U)).
Next Obligation.
Proof.
  rename x into f, y into g. 
  exists (inverse [X]).
  econstructor; rename X into α.
  intro u. eapply inverse; eapply composition. apply comp. apply identity.
  apply (eq_section α).
  eapply composition. apply assoc. 
  eapply composition. apply comp. eapply composition. eapply inverse.
  apply (ExLawComp_nat _ _ _ _ u).
  eapply composition. 
  eapply nat_comp2. apply (Equiv_adjoint_inv _). 
  apply (inv_R (GroupoidP := nat_trans_grp T U)).
  apply (nat_comp_id _ _ u). apply identity. apply id_R.
Defined.

Program Instance Comp_Equiv_eq T U : Composition (Equiv_eq (T:=T) (U:=U)).

Next Obligation. 
Proof.
  rename x into f, y into g, z into h, X into H, X0 into H'. 
  exists (composition [H] [H']).
  rename H into α. rename H' into β. 
  econstructor. intro u. eapply composition. apply (eq_section α). 
  eapply composition. apply comp. apply identity.
  apply (eq_section β). eapply composition. apply assoc.
  apply comp; try apply identity. 
  eapply composition. eapply inverse. 
  apply (ExLawComp_nat _ _ _ _ u).
  apply (fun a b => nat_comp2 a b u); try apply identity .
  eapply inverse, Equiv_adjoint_comp.
Defined.

Instance Equiv_eqHom T U : HomT1 (Equiv T U) := 
  {eq1 := Equiv_eq (T:=T) (U:=U) }.

Definition Equiv_eq2 T U (f g : Equiv T U) : HomT (Equiv_eq f g) :=
  λ (e e' : Equiv_eq f g), [e] ~ [e'].

Instance Equiv_eq2Hom T U : HomT2 (Equiv_eq (T:=T) (U:=U)) := 
  {eq2 := Equiv_eq2 (T:=T) (U:=U) }.

Instance Equiv2_id T U (f g : T <~> U) : 
  Identity (Equiv_eq2 (f:=f) (g:=g)) := 
  { identity x t := identity _ }.

Program Instance Equiv2_inv T U (f g : T <~> U) : 
  Inverse (Equiv_eq2 (f:=f) (g:=g)) :=
  { inverse X Y e t := inverse (e t) }.

Program Instance Equiv2_comp T U (f g : T <~> U) : 
  Composition (Equiv_eq2 (f:=f) (g:=g)) :=
  { composition X Y Z e e' t := composition (e t) (e' t) }.

Program Instance Equiv_eq_cat T U : CategoryP (Equiv_eq2Hom T U).
Next Obligation. intro t. destruct f. apply id_R. Defined.
Next Obligation. intro t. destruct f; apply id_L. Defined.
Next Obligation. intro t. destruct f, g, h. apply assoc. Defined.
Next Obligation. 
  intro t. destruct f, g, f', g'. 
  apply comp. apply X. apply X0 . 
Defined.

Program Instance Equiv_eq_grp T U : GroupoidP (Equiv_eq_cat T U).
Next Obligation. intro t. destruct f; apply inv_R. Defined.
Next Obligation. intro t. destruct f; apply inv_L. Defined.
Next Obligation. intro t. destruct f, f'; apply inv, X. Defined.

Program Instance Equiv_eq2_cat T U (f g : T <~> U) : 
  Equivalence (Equiv_eq2 (f:=f) (g:=g)).

Program Instance Equiv_2category T U : WeakCategory (T <~> U) | 10 := 
  {| Hom1 := Equiv_eqHom T U; Hom2 := Equiv_eq2Hom T U|}.

Program Instance __Equiv_eq_group T U : WeakGroupoid (T <~> U).

(* Next Obligation. *)
(* Proof. *)
(*   unfold Equiv_2category in E. simpl in E. red in E. *)
(*   unfold Equiv_2category in E'. simpl in E'. red in E'. *)
(*   (* Here we assume all modifications are equal *) *)
(*   admit. *)
(* Qed. *)

Definition section_comp_l (X Y Z : WeakGroupoidType) 
           (f : X <~> Y) (g : Y <~> Z) (z : [Z]) :=
  (section (g ° f) @ z).

Lemma section_comp (X Y Z : WeakGroupoidType) 
      (f : X <~> Y) (g : Y <~> Z) (z : [Z]) :
  section_comp_l f g z ~ (section g @ z) ° map [g] (section f @ (adjoint g @ z)).
Proof.  
  unfold section_comp_l. simpl. simpl_id_bi'.
Defined.

Definition retraction_comp_l (X Y Z : WeakGroupoidType) 
           (f : X <~> Y) (g : Y <~> Z) (z : [X]) :=
  retraction (g ° f) @ z.

Lemma retraction_comp X Y Z (f : X <~> Y) (g : Y <~> Z) z :
  retraction_comp_l f g z ~ 
  [retraction f] z ° map (adjoint f) ([retraction g] ([[f]] z)).
Proof. 
  unfold retraction_comp_l.
  simpl. simpl_id_bi'.
Defined.

Hint Extern 1 (@CategoryP (proj1 ?T) (@Hom1 ?T) _) => exact (T.(proj2).(Category_1)) : typeclass_instances.

Lemma Equiv_adjoint_idR X Y (f : X <~> Y)
      (H := nat_id_R [f]:[f ° identity X] ~1 [f]) (y : [Y]) :
  Equiv_adjoint H @ y ~ identity (adjoint f) @ y.
  eapply composition. apply Equiv_adjoint_simpl. simpl.
  unfold id, _Equiv_comp_obligation_1.
  simpl_id'. simpl_id'. simpl. apply (triangle_inv' f).
Defined.

Lemma Equiv_adjoint_idL X Y (f : X <~> Y) 
      (H := (nat_id_L [f]:[identity _°f] ~1 [f])) (y : [Y]) :
   Equiv_adjoint H @ y ~ identity (adjoint f) @ y.
Proof.
  eapply composition. apply Equiv_adjoint_simpl. simpl.
  unfold id, _Equiv_comp_obligation_1.
  simpl_id'. apply (triangle_inv' f).
Defined.

Program Instance EquivHom : HomT1 WeakGroupoidType := {eq1 := Equiv}.

Program Instance Equiv_eqHom' : HomT2 Equiv := {eq2 := Equiv_eq}.

Print Hom2.

Definition Equiv_adjoint_assoc (X Y Z W : WeakGroupoidType)
        (f : X <~> Y) (g : Y <~> Z) (h : Z <~> W) (w:[W]) 
        (H := (nat_assoc [f] [g] [h] : [(h ° g) °f] ~1 [h ° (g ° f)])) :
    Equiv_adjoint H @ w ~ identity (adjoint ((h ° g) °f)) @ w.
Proof.
  eapply composition. apply Equiv_adjoint_simpl. simpl.
  simpl_id'.
  eapply composition. apply comp. eapply composition. eapply inverse. 
  apply comp_inv. apply comp. eapply composition. eapply inverse. 
  apply comp_inv. apply comp. apply identity.
  eapply composition. eapply inverse. apply map_inv. 
  eapply (map2 (adjoint f)). apply identity. 
  eapply composition. eapply inverse. simpl.
  apply map_inv. 
  eapply (map2 (adjoint f)). 
  eapply composition. eapply inverse. apply map_inv. 
  eapply (map2 (adjoint g)). apply identity. apply identity.
  eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity.
  eapply composition. eapply inverse. apply (map_comp (adjoint f)).
  eapply _map2. eapply composition. eapply inverse. apply (map_comp (adjoint g)).
  eapply _map2. eapply composition. apply comp. apply identity. eapply composition. 
  apply _map_comp.
  apply comp. apply identity. apply _map_comp.
  eapply composition. apply assoc. eapply composition. apply comp.
  eapply inverse.
  (* The anotation is necessary as typeclass resolution 
     is run only after unification *)
  apply (α_map (@inverse _ _ (nat_inv Z Z) _ _ (retraction h))).
  apply identity.
  eapply composition. apply assoc. eapply composition. apply comp.
  eapply composition. eapply inverse. apply assoc.  apply comp.
  apply identity.   eapply inverse. 
  apply (α_map (inverse (Inverse:=nat_inv Z Z) (retraction h))).
  apply identity.
  eapply composition. eapply inverse. apply assoc. eapply composition. apply comp.
  apply identity. eapply composition. eapply inverse. apply assoc. 
  eapply composition. apply comp.
  apply identity. apply (triangle_inv' h). apply id_L. apply identity.
  simpl. unfold id. 
  eapply composition. eapply inverse. apply assoc. 
  eapply composition. apply comp. apply identity. 
  eapply composition. eapply inverse. apply _map_comp.
  eapply _map2. eapply composition. apply comp. apply identity. 
  apply _map_comp.
  eapply composition. apply assoc. eapply composition. apply comp.
  eapply inverse. 
  apply (α_map (@inverse _ _ (nat_inv _ _) _ _ (retraction g))). apply identity.
  eapply composition. eapply inverse. apply assoc. eapply composition. apply comp.
  apply identity. apply (triangle_inv' g). apply id_L.
  apply (triangle_inv' f).
Defined.

Program Instance Equiv_cat : CategoryP Equiv_eqHom'.
Next Obligation. 
  set (H := nat_id_R [f] : [f ° identity x] ~1 [f]). exists H. 
  econstructor. intro.
  eapply composition. apply section_comp.
  eapply composition. apply comp. apply (map_id [f]). apply identity.
  eapply inverse. eapply composition. apply comp.
  eapply composition. apply id_R. apply identity. apply identity.
  eapply composition. apply comp. eapply composition. eapply (map2 [f]).
  apply Equiv_adjoint_idR. simpl. apply (map_id [f]). apply identity. 
  apply identity.
Defined.

Next Obligation. 
  set (H := nat_id_L [f] :[identity y ° f] ~1 [f]). exists H. 
  econstructor. intro. simpl. simpl_id_bi'.
  eapply composition. apply comp. eapply (map2 [f]).
  apply Equiv_adjoint_idL. apply identity. 
  eapply composition; try apply id_R. apply comp; [idtac | apply identity].
  apply map_id.
Defined.
Next Obligation. 
  exists (nat_assoc [f] [g] [h]).
  econstructor. intro. simpl.
  simpl_id_bi'. 
  eapply composition. apply assoc. eapply inverse.
  eapply composition. apply assoc. apply comp; [idtac |
                                                apply identity].
  eapply inverse. 
  eapply composition. apply comp. apply identity.
  apply (map_comp [h]). 
  eapply composition. apply assoc. apply comp; [idtac |
                                                apply identity].
  eapply composition; try apply id_R. 
  apply comp; [idtac | apply identity].
  eapply composition; try apply (map_id [h]). 
  apply (map2 [h]).
  eapply composition; try apply (map_id [g]). 
  apply (map2 [g]).
  eapply composition; try apply (map_id [f]). 
  apply (map2 [f]). apply Equiv_adjoint_assoc.
Defined.
(* The fellowing admitted proof is not difficult in essence, and are
                 similar to the previous one. *) 
Next Obligation. 
  exists (nat_comp' [X] [X0]). 
  apply AllEquivEq.
Defined.

Program Instance Equiv_grp : GroupoidP Equiv_cat.
Next Obligation. 
  exists (section f).
  econstructor; intro; simpl; simpl_id_bi'.
  eapply composition. apply comp. apply identity.
  apply (Equiv_adjoint_simpl (f := f ° inverse f) (f' := identity y) (section f)).
  simpl. unfold id.
  simpl_id'. eapply composition. apply assoc.
  eapply composition; try apply id_R.
  apply comp; [idtac | apply identity].
  apply inv_L.
Defined.
Next Obligation. exists (retraction f). 
                 apply AllEquivEq.
Defined.
Next Obligation. exists (Equiv_adjoint [X]). apply AllEquivEq.
Defined.

Program Instance Equiv_eq2_equ T U (f g : T <~> U) :
  Equivalence (Equiv_eq2 (f:=f) (g:=g)).

Program Instance Equiv_eqEquivalence T U : Equivalence (Equiv_eq (T:=T) (U:=U)).

Program Instance Equiv_WeakCategory : WeakCategory WeakGroupoidType := 
  {| Hom1 := EquivHom ; Hom2 := Equiv_eqHom'|}.

Program Instance Equiv_WeakGroupoid : WeakGroupoid WeakGroupoidType.

(* Next Obligation.  *)
(* Proof. *)
(*   intros. *)
  
(*   (* We're supposing all natural transformations are equal. *) *)
(*   admit. *)
(* Qed. *)

(* end hide *)

(**
 In the definition below, [Equiv_WeakGroupoid] is a proof that [Equiv] and [Equiv_eq] form a weak groupoid. 
 *)

Definition _Type : WeakGroupoidType := 
  (WeakGroupoidType ; Equiv_WeakGroupoid).

(** 
  %\noindent%
  As [WeakGroupoidType] appears both in the term and in the type, the use of polymorphic universe is crucial
  to avoid inconsistency. 
 
*)

(* begin hide *)

Notation equiv_assoc := (@assoc Equiv_cat).
Notation equiv_comp  := (@comp  Equiv_cat).
Notation equiv_id_R  := (@id_R  Equiv_cat). 
Notation equiv_id_L  := (@id_L  Equiv_cat).

Notation equiv_inv_R  := (@inv_R  Equiv_grp). 
Notation equiv_inv_L  := (@inv_L  Equiv_grp).
Notation equiv_inv  := (@inv Equiv_grp).

Ltac compose := eapply composition.

Ltac simpl_id_end := 
  match goal with
    | [ |- eq2 (?P ^-1 ° ?P) _] => compose;
       [first [apply inv_L | apply equiv_inv_L]|idtac]
    | [ |- eq2 (?P ° ?P ^-1) _] => compose;
       [first [apply inv_R | apply equiv_inv_R]|idtac]
    | [ |- eq2 (?P ° identity ?x) _] => compose;
       [first [apply id_R | apply equiv_id_R]|idtac]
    | [ |- eq2 (identity ?x ° ?P) _] => compose;
       [first [apply id_L | apply equiv_id_L]|idtac]
    | [ |- eq2 ((?P ^-1) ^-1) _] => compose;
       [first [apply inv_inv | apply (@inv_inv _Type)]|idtac]
    | [ |- eq2 ((identity _) ^-1) _] => compose;
       [first [apply inv_id | apply (@inv_id _Type)]|idtac]
    | [ |- Equiv_eq (?P ^-1 ° ?P) _] => compose; [apply equiv_inv_L|idtac]
    | [ |- Equiv_eq (?P ° ?P ^-1) _] => compose; [apply equiv_inv_R|idtac]
    | [ |- Equiv_eq (?P ° identity ?x) _] => compose; [apply equiv_id_R|idtac]
    | [ |- Equiv_eq (identity ?x ° ?P) _] => compose; [apply equiv_id_L|idtac]
    | [ |- Equiv_eq ((?P ^-1) ^-1) _] => compose; [apply (@inv_inv _Type)|idtac]
    | [ |- Equiv_eq ((identity _) ^-1) _] => compose; [apply (@inv_id _Type)|idtac]
  end.

Ltac simpl_id_end_extended := first [ simpl_id_end |
                                      match goal with
                   | [ |- Equiv_eq ?e _ ] => apply (identity e)
                   | [ |- eq2 ?e _ ] => apply (identity e)
                   | [ |- _ ] => idtac
                 end].

Ltac simpl_id := first [simpl_id_end ; simpl_id |
  lazymatch goal with
    | |- context [identity _] => fail
    | |- _ => apply identity
  end|
  match goal with
    | [ |- eq2 (?P ^-1) _] =>
      eapply composition;
        [first [apply equiv_inv | apply inv] ; simpl_id | idtac]; 
        try apply identity
    | [ |- eq2 (map ?F (identity _)) _] => 
      eapply composition;
        [eapply (map_id F); simpl_id | idtac]; 
        simpl_id
    | [ |- Equiv_eq (map ?F (identity _)) _] => 
      eapply composition;
        [eapply (map_id F); simpl_id | idtac]; 
        simpl_id
    | [ |- eq2 (map ?F ?P) _] => 
      first [eapply composition;
              [eapply (map2 F); simpl_id | idtac]; 
              [apply identity | idtac] | 
             (progress_evars (eapply composition;
                              [eapply (map2 F); simpl_id | idtac];instantiate));
               simpl_id |idtac]
    | [ |- Equiv_eq (map ?F ?P) _] => 
      first [eapply composition;
              [eapply (map2 F); simpl_id | idtac]; 
              [apply identity | idtac] | 
             (progress_evars (eapply composition;
                              [eapply (map2 F); simpl_id | idtac];instantiate));
               simpl_id |idtac]
    | [ |- Equiv_eq (?P ^-1) _] =>
      eapply composition;
        [apply equiv_inv; simpl_id | idtac]; 
        try apply identity
    | [ |- Equiv_eq (?Q ° ?P) _] =>
      eapply composition;
        [apply equiv_comp ; simpl_id | idtac];
        simpl_id_end_extended
    | [ |- Equiv_eq ?e _ ] => apply (identity e)
    | [ |- eq2 (?Q ° ?P) _] =>
      eapply composition;
        [first [apply comp |
                apply equiv_comp] ; simpl_id | idtac];
        simpl_id_end_extended
    | [ |- eq2 ?e _ ] => first [has_evar e; idtac | apply (identity e)]
    | [ |- _ ] => idtac
  end].


Ltac simpl_id_bi := simpl_id; eapply inverse; simpl_id.

(* end hide *)

(**  

** Rewriting in homotopy type theory
  %\label{sec:rew}%

  When considering a dependent type [F: [A --> _Type]], the [map] function 
  provides a homotopic equivalence between [F @ x] and [F @ y] for any [x]
  and [y] such that [x ~1 y]. The underlying map of homotopic equivalence
  can hence be used to cast any term of type [[F @ x]] to [[F @ y]].
*)

Definition eq_rect A {x y : [A]} (F: [A --> _Type]) 
  (e : x ~1 y) : (F @ x) ---> (F @ y) := [map F e].


(** Using compatibility on [map], we can reason on different paths of
  rewriting.  Intuitively, any two rewriting maps with the same domain
  and codomain should be the same up to homotopy. As we only consider
  weak groupoids, there is only one relevant level of compatibilities,
  higher compatibilities are trivial. [eq_rect_eq] is an example of a
  derivable equality between two rewriting maps, when the proofs
  relating [x] and [y] are equal.  *)


Definition eq_rect_eq A {x y : [A]} (F: [A --> _Type]) 
  {e e': x ~1 y} (H : e ~ e') : eq_rect F e ~1 eq_rect F e' :=
  [map2 F H].

(** %\noindent% In the text, 
  we also use [eq_rect_id], [eq_rect_comp] and [eq_rect_map].
*)


(* begin hide *)

Definition eq_rect_map (A : [_Type]) {x y} (F: [A --> _Type]) 
  {p q : [F @ x]} (e : x ~1 y) (H : p ~1 q) : 
  (eq_rect F e) @ p ~1 (eq_rect F e) @ q :=
  map [map F e] H.


Definition eq_rect_comp (A : [_Type]) {x y z : [A]} (F: [A --> _Type])
  (e : x ~1 y) (e' : y ~1 z) : 
  eq_rect F (e' ° e) ~1 eq_rect F e' ° eq_rect F e :=  
  [map_comp F e e'].

Definition eq_rect_id (T:[_Type]) (F : [T --> _Type]) {x : [T]}
  : eq_rect F (identity x) ~1 identity _ := 
  [map_id F].

Definition eq_rect_inv (A : [_Type]) (x : [A]) (F: [A --> _Type]) 
  (y : [A]) (e : x ~1 y) : eq_rect F (inverse e) ° eq_rect F e ~1 identity _. 
Proof. 
  eapply composition. eapply inverse; apply eq_rect_comp; auto.
  eapply composition. exact (eq_rect_eq _ (inv_L _ _ e)).
  apply eq_rect_id. 
Defined.

(* end hide *)

(* begin hide *)

Ltac trunc_eq := match goal with                    
                     | [ |- eq2 ?e ?e'] => 
                       rewrite (Trunc_2 (T := _Type) _ _ _ _ e e'); 
                         apply identity
                   end.
       
Lemma map2_id : forall T (f : [T --> _Type]) {x y:[T]} (e: x ~1 y), 
                  map2 f (identity e) ~2 identity (map f e).
Proof. intros. trunc_eq. Defined.

Lemma map2_comp : forall T (f : [T --> _Type]) {x y:[T]} (e e' e'':x ~1 y) 
                       (E:e ~2 e') (E':e'~2 e''),
                    map2 f (E' ° E) ~2 map2 f E' ° map2 f E.
Proof. intros. trunc_eq. Defined.

Lemma map2_id_L : ∀ T (f : [T --> _Type]) {x y : [T]} (e:x ~1 y),
  map2 f (id_L' e) ~2 
  id_L' (map f e) ° (identity (map f e) ** map_id f) ° map_comp f _ _. 
Proof. intros. trunc_eq. Defined.

Lemma map2_id_R : ∀ T (f : [T --> _Type]) {x y : [T]} (e:x ~1 y),
  map2 f (id_R' e) ~2 
  id_R' (map f e) ° (map_id f ** identity (map f e)) ° map_comp f _ _.
Proof. intros. trunc_eq. Defined.

Definition assoc'' {T} {Hom1 : HomT1 T} {Hom2: HomT2 eq1} {Category} 
           {x y z w : T} {e e' e''} := 
  assoc (CategoryP := Category) x y z w e e' e''.

Lemma map2_assoc : ∀ T (f : [T --> _Type]) {x y z w : [T]} 
                     (e:x ~1 y) (e':y ~1 z) (e'':z ~1 w),
  assoc'' ° (identity _ ** map_comp f e' e'')  ° map_comp f e (e'' ° e')  ~
  (map_comp f _ _ ** identity _) ° map_comp f (e' ° e) e'' ° map2 f assoc''.
Proof. intros. trunc_eq. Defined.

Lemma map2_comp' : ∀ T (f : [T --> _Type]) {x y z : [T]} 
                     (e e':x ~1 y) (g g':y ~1 z) 
                     (E : e ~2 e') (E' : g ~2 g'),
  map_comp f _ _ ° map2 f (comp _ _ _ _ _ _ _ E E') ~ 
  comp _ _ _ _ _ _ _ (map2 f E) (map2 f E') ° map_comp f _ _.
Proof. intros. trunc_eq. Defined.

Lemma map3 : ∀ T (f : [T --> _Type]) {x y : [T]} (e e' : x ~1 y) (E E' : e ~2 e'),
               map2 f E ~2 map2 f E'.
Proof. intros. trunc_eq. Defined.

(* end hide *)


(** 
** Dependent Product 
  %\label{sec:depprod}%

  As for functions, dependent functions will be interpreted as functors. 
  But this time, the compatibilities with higher-order morphisms cannot
  be expressed as simple equalities, as some rewriting has to be done to 
  make those equalities typable. We call such a functor a 
  %\emph{dependent functor}%.
*)

Class WeakDependentFunctor (Γ:[_Type]) (U : [Γ --> _Type]) 
  (f : ∀ t, [U @ t]) : Type := {
  _Dmap      : ∀ {x y} (e: x ~1 y), eq_rect U e @ (f x) ~1 f y ;
  _Dmap_comp : ∀ x y z (e : x ~1 y) (e' : y ~1 z),
   _Dmap (e' ° e) ~2 _Dmap e' ° eq_rect_map U _ (_Dmap e) ° 
                     (eq_rect_comp U e e' @ _);
  _Dmap2  : ∀ (x y : [Γ]) (e e': x ~1 y) (H: e ~ e'),
    _Dmap e ~ _Dmap e' ° (eq_rect_eq U H @ (f x))}.

Definition Prod_Type (T:[_Type]) (U:[T --> _Type]) :=
  {f : ∀ t, [U @ t] & WeakDependentFunctor U f}.

(* begin hide *)

Hint Extern 0 (WeakDependentFunctor _ [?f]) => exact (proj2 f) : typeclass_instances.

Print _Dmap_comp.

Notation "'Dmap' f" := (@_Dmap _ _ _ (proj2 f) _ _) (at level 0, f at level 0).
Notation "'Dmap_comp' f" := (@_Dmap_comp _ _ _ (proj2 f) _ _ _) (at level 0, f at level 0).
Notation "'Dmap2' f" := (@_Dmap2 _ _ _ (proj2 f) _ _ _ _) (at level 0, f at level 0).

Definition Dmap_id {T:[_Type]} {U:[T --> _Type]} (f: Prod_Type U) {x: [T]} : 
  Dmap f (identity x) ~ eq_rect_id U @ (f @ x).
Proof.  
  eapply right_simplify'. eapply right_simplify'.
  eapply composition. eapply inverse. eapply (Dmap_comp f). 
  eapply composition. eapply (Dmap2 f (id_L _ _ (identity x))).
  unfold eq_rect_eq, eq_rect_map, eq_rect_comp, eq_rect_id. 
  apply inverse. eapply composition. apply comp. apply identity.
  apply (α_map [map_id U]). eapply composition. apply assoc.
  apply comp; [idtac | apply identity]. apply inverse.
  eapply composition. apply map2_id_L.
  simpl. unfold id. simpl_id_bi'.  
Defined. 

Opaque Dmap_id.



(* end hide *)

(** 

  Equality between dependent functors is given by dependent natural transformations. 
  Again, at level 2, the naturality condition is trivial.

*)

Class DNaturalTransformation T (U:[T --> _Type]) 
 {f g: Prod_Type U} (α : ∀ t : [T], f @ t ~1 g @ t) := 
  {_α_Dmap : ∀ {t t'} e, (α t') ° (Dmap f e) ~
    (Dmap g e) ° eq_rect_map U e (α t)}.

Definition Dnat_trans T (U:[T --> _Type]) (f g: Prod_Type U)  :=
  {α : ∀ t : [T], f @ t ~1 g @ t & DNaturalTransformation α}.


(* begin hide *)

Hint Extern 0 (DNaturalTransformation [?f]) => exact (proj2 f) : typeclass_instances.
Notation α_Dmap f := (@_α_Dmap (proj2 f) _ _).

Program Instance Dnat_id T U : Identity (Dnat_trans (T:=T) (U := U)).
Next Obligation. 
  rename x into f. exists (λ t , identity (f @ t)).
  intros. unfold eq_rect_map. econstructor. intros.
  eapply composition. apply id_L.
  eapply inverse. eapply composition. eapply comp. 
  apply (map_id [map U e]). 
  apply identity. apply id_R. 
Defined.
 
Program Instance Dnat_inv T U : Inverse (Dnat_trans (T:=T) (U := U)).
Next Obligation. 
  rename x into f, y into g, X into  H. 
  exists (λ t , inverse (H @ t)).
  intros. unfold eq_rect_map. destruct H as [H Hmap]. simpl in *.
  econstructor. intros.
  eapply inverse. unfold eq_rect_map in Hmap. eapply right_simplify'.
  eapply composition. apply assoc.
  eapply composition. apply comp. 
  eapply composition. apply comp. apply identity. apply map_inv.
  apply inv_L. apply identity.
  eapply composition. apply id_R.
  eapply inverse. eapply composition. 
  eapply composition. apply assoc.
  eapply composition. apply comp. eapply inverse; apply Hmap. apply identity.
  eapply composition. eapply inverse.  apply assoc.
  apply comp. apply identity. apply inv_L.
  apply id_L.
Defined.

Program Instance Dnat_comp T (U:[T --> _Type]) : 
  Composition (Dnat_trans (U := U)).
Next Obligation. 
  rename x into f, y into g, z into h, X into H, X0 into H'. 
  exists (λ t , composition (H @ t) (H' @ t)).
  intros. unfold eq_rect_map. econstructor. intros. eapply inverse.
  eapply composition. apply comp. 
  apply _map_comp.
  apply identity.
  eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity. 
  eapply inverse. apply (Π2 H'). 
  eapply composition. apply assoc.
  eapply composition. apply comp. eapply inverse, (Π2 H). apply identity. 
  eapply composition. eapply inverse.  apply assoc. apply identity. 
Defined.

Program Instance Dnat_transHom T (U:[T --> _Type]) : HomT1 (Prod_Type U) := 
  {eq1 := Dnat_trans (T:=T) (U:=U)}.

(* end hide *)

Definition Dmodification T U (f g : Prod_Type U) : HomT (f ~1 g) 
  := λ α β , ∀ t : [T], α @ t ~ β @ t.

Arguments Dmodification [T] [U] f g _ _.

(* begin hide *)

Program Instance DmodificationHom T U : HomT2 eq1 := 
  {eq2 := @Dmodification T U}.

Program Instance Dnat2_id T (U:[T --> _Type]) (f g : Prod_Type U) : 
  Identity (Dmodification f g) :=
  { identity x t := identity _ }.

Program Instance Dnat2_inv T (U:[T --> _Type]) (f g : Prod_Type U) : 
  Inverse (Dmodification f g) :=
  { inverse X Y t x := inverse (t x) }.

Program Instance Dnat2_comp T (U:[T --> _Type]) (f g : Prod_Type U) : 
  Composition (Dmodification f g) :=
  { composition X Y Z f g x := composition (f x) (g x) }.

Program Instance Dnat_trans_cat T (U:[T --> _Type]) : 
  CategoryP (DmodificationHom U).
Next Obligation. intro t. apply id_R. Defined.
Next Obligation. intro t. apply id_L. Defined.
Next Obligation. intro t. apply assoc. Defined.
Next Obligation. intro t. apply comp. apply X. apply X0. 
Defined.

Program Instance Dnat_trans_grp T U : GroupoidP (Dnat_trans_cat T U).
Next Obligation. intro t. apply inv_R. Defined.
Next Obligation. intro t. apply inv_L. Defined.
Next Obligation. intro t. apply inv, X. Defined.

Program Instance Dmodification_equiv T (U:[T --> _Type]) (f g : Prod_Type U) :
  Equivalence (Dmodification f g).

Program Instance Dnat_2category T (U:[T --> _Type]) : 
  WeakCategory (Prod_Type U) :=
  {| Hom1 := Dnat_transHom U; Hom2 := DmodificationHom U|}.

(* end hide *)

(** We can now equip dependent functors with a groupoid structure
    using [Dnat_trans] and [Dmodification] as underlying equalities.
 *)

(* begin hide *)

Program Instance prod_weakgroupoid T (U:[T --> _Type]) : 
  WeakGroupoid (Prod_Type U).

(* Next Obligation. *)
(* Proof. *)
(*   unfold Equiv_2category in E. simpl in E. red in E. *)
(*   unfold Equiv_2category in E'. simpl in E'. red in E'. *)
(*   (* Here we assume all Dmodifications are equal *) *)
(*   admit. *)
(* Qed. *)

  
(* end hide *)

Definition _Prod T (U:[T --> _Type]) := (Prod_Type U ; prod_weakgroupoid U).


(**

  ** Dependent sums
  %\label{sec:sigma}%

  In the interpretation of Σ types, trivial equalities coming from the
  truncation at level 2 of $\infty$-groupoids become more
  apparent.  
  This is because, in the same way that a Σ type on a fibration [U : T ->
  Type] in Coq lives in universe [n + 1] when [U] lives in universe
  [n], our interpretation of Σ type requires that [U] defines
  n-groupoids to get a n+1-groupoid $\Sigma$ type.  
*)

Definition sum_type T (U : [T --> _Type]) := {t : [T] & [U @ t]}.

(**

  The 1-equality between dependant pairs is given by 1-equality on the
  first and second projections, with a transport on the second
  projections.

*)

Definition sum_eq T (U : [T --> _Type]) := λ (m n : sum_type U), 
   {P : [m] ~1 [n] & eq_rect U P @ (Π2 m) ~1 Π2 n}.

(* begin hide *)

Set Program Mode.

Program Instance sum_id T U : Identity (sum_eq (T:=T) (U:=U)) :=
  { identity x := (identity (Π1 x) ;eq_rect_id _ @ Π2 x) }.

Program Instance sum_inv T U: Inverse (sum_eq (T:=T) (U:=U)).
Next Obligation. 
Proof. 
  rename x into m, y into n, X into H. 
  exists (inverse [H]).
  apply (Equiv_injective (map U [H])).
  eapply composition; try exact (inverse (Π2 H)). unfold eq_rect. 
  assert (map_inv_R : forall {T U} (U : T ---> U) x y (e : x ~1 y),
                        map U e ° map U (inverse e) ~ identity (U @ y)). 
  - intros. eapply composition. apply comp. apply map_inv. 
    apply identity. apply inv_R.
  - apply ([map_inv_R T _ U _ _ _] @ (Π2 n)).
Defined.

Program Instance sum_comp T U : Composition (sum_eq (T:=T) (U:=U)).
Next Obligation. 
  rename x into m, y into n, z into p, X into H1, X0 into H2. 
  exists ([H2] ° [H1]). 
  eapply composition. 
  apply (eq_rect_comp U [H1] [H2]).
  eapply composition; [idtac | exact (Π2 H2)].
  unfold composition. simpl. unfold eq_rect.  
  apply (map [map U [H2]] (Π2 H1)).
Defined.

Program Instance sum_eqHom T (U : [T --> _Type]) : HomT1 (sum_type U) := 
  {eq1 := sum_eq (T:=T) (U:=U)}.


(* end hide *)

(** 
  In the same way, 2-equality between 1-equalities is given by projections
  and rewriting.
*)
(* begin hide *)

Definition sum_eq2 T (U : [T --> _Type]) (M N : sum_type U) : 
  HomT (M ~1 N) := λ e e' , {P : [e] ~ [e'] & 
         Π2 e ~ Π2 e' ° (eq_rect_eq U P @ (Π2 M))}.

Program Instance sum_eq2_id T U (M N : sum_type (T:=T) U) :
  Identity (sum_eq2 (M:=M) (N:=N)).
Next Obligation. 
  exists (identity _).
  eapply inverse. eapply composition.
  apply comp. apply (map2_id U [x] (Π2 M)).
  apply identity. apply id_R.
Defined.

Lemma map_inv2 {T} (f : [T --> _Type]) :
  ∀ x y (e e' : x ~1 y) (E : e ~2 e') , 
    map2 f (inverse E) ~2 inverse (map2 f E).
Proof.
  intros. trunc_eq.
Defined.

Program Instance sum_eq2_inv T U (M N : sum_type (T:=T) U) :
  Inverse (sum_eq2 (M:=M) (N:=N)).
Next Obligation.
  exists (inverse [X]). 
  eapply inverse. eapply composition.
  apply comp.
  
  apply (map_inv2 U _ _ _ _ [X]). apply identity.
  unfold sum_eq2 in X. unfold eq_rect_eq in X.
  eapply (right_simplify_gen). intros. exact (Equivalence_2 x0 y0).
  apply inv_R.
  eapply composition. Focus 2. apply (Π2 X).
  eapply composition. apply assoc.
  eapply composition. apply comp. apply inv_L. apply identity.
  apply id_R.
Defined.

Program Instance sum_eq2_comp T U (M N : sum_type (T:=T) U) :
  Composition (sum_eq2 (M:=M) (N:=N)).
Next Obligation.
 exists (composition [X] [X0]). 
  eapply inverse. eapply composition.
  apply comp. apply (map2_comp U _ _ _ [X] [X0] (Π2 M)). apply identity.
  eapply composition. eapply inverse. apply  assoc.
  eapply composition. apply comp. apply identity. eapply inverse, X0.
  eapply inverse, X.
Defined.

(* begin hide *)

Program Instance sum_eq2Hom T (U : [T --> _Type])  : HomT2 (sum_eq (U:=U)) := 
  {eq2 := sum_eq2 (T:=T) (U:=U)}.

Program Instance sum_eq2_eq T U (M N : sum_type (T:=T) U) :
  Equivalence (sum_eq2 (M:=M) (N:=N)).

Program Instance sum_category2 T U : CategoryP (sum_eq2Hom (T:=T) U).

Next Obligation.
  exists (id_R _ _ [f]). unfold eq_rect_eq. simpl.
  eapply composition. apply assoc. apply comp; try apply identity.
  unfold eq_rect_comp, eq_rect, eq_rect_id. 
  eapply inverse. eapply composition. apply (map2_id_R U [f]).
  simpl. apply comp. apply identity. eapply composition. apply id_L. apply id_R.
Defined.

Next Obligation.
  exists (id_L _ _ [f]). unfold eq_rect_eq. simpl.
  unfold eq_rect_comp, eq_rect, eq_rect_id. 
  eapply inverse. eapply composition. apply comp.
  apply (map2_id_L U [f]). apply identity. simpl.
  eapply composition. eapply inverse. apply assoc. apply comp. apply identity.
  eapply composition. apply comp. eapply composition. apply id_L.
  eapply composition. apply id_L. apply identity. apply identity. 
  eapply inverse. apply (α_map [map_id U]).
Defined.

Next Obligation.
  exists (assoc _ _ _ _ [f] [g] [h]). simpl. 
  unfold eq_rect_comp, eq_rect, eq_rect_eq.
  eapply composition. apply assoc. eapply composition. apply assoc.
  eapply composition. apply assoc. eapply inverse.
  eapply composition. apply assoc. eapply composition. apply assoc.
  apply comp; try apply identity. eapply composition. apply comp. apply identity.
  eapply composition.  
  apply (map_comp [map U [h]]). apply comp.
  apply identity.
  apply (map_comp [map U [h]]). eapply composition. apply assoc.
  eapply composition. apply assoc.
  apply comp; try apply identity. eapply composition. apply comp.
  eapply composition. apply comp. apply identity. eapply inverse. apply id_R. 
  eapply composition. eapply inverse. apply assoc.
  eapply inverse. apply (map2_assoc U [f] [g] [h] (Π2 x)). apply identity. simpl.
  unfold arrow_comp_obligation_1. eapply composition. apply comp. 
  apply comp. apply identity. apply id_L. apply identity.
  eapply composition. eapply inverse. apply assoc.
  eapply inverse. eapply composition. eapply inverse. apply assoc.
  apply comp; try apply identity. eapply inverse.
  simpl_id. apply inverse.
  apply (α_map [map_comp U [g] [h]]). 
Defined.

Next Obligation.
  exists (comp _ _ _ _ _ _ _ [X] [X0]). simpl.
  unfold eq_rect_comp, eq_rect, eq_rect_eq.
  eapply composition. apply assoc. eapply composition. 
  apply comp. apply identity. apply (Π2 X0). eapply composition. apply assoc. 
  eapply inverse. eapply composition. apply assoc. eapply composition. apply assoc.
  apply comp; try apply identity. unfold eq_rect_eq. 
  eapply inverse. eapply composition. eapply inverse. apply assoc. 
  eapply composition. apply comp.
  apply identity. apply (α_map [map2 U [X0]]). 
  eapply composition. apply assoc. eapply composition. 
  apply comp. apply identity.
  eapply composition.
  apply (map2 [map U [g']] ( Π2 X)).
  apply (map_comp [map U [g']]).
  eapply composition. apply assoc. apply comp; [idtac | apply identity].
  eapply inverse. eapply composition. apply map2_comp'. simpl.
  unfold eq_rect_eq. eapply composition. apply assoc. apply identity.
Defined.

Lemma id_R'' (T : WeakCatType) (x y : [T]) (f g : x ~1 y) : 
  f ~2 g -> f ° identity x ~2 g.
Proof. intros. eapply composition. apply id_R'. apply X. Defined.

Program Instance sum_groupoid2 (T : [_Type]) (U : [T --> _Type]) :
  GroupoidP (sum_category2 T U).
Next Obligation. 
Proof. 
  exists (inv_R _ _ _).
  (* simpl. *)
  (* unfold eq_rect_comp, eq_rect, eq_rect_eq, eq_rect_id. *)
  (* unfold Equiv_injective. simpl.  *)
  (* Time simpl_id. *)
  (* eapply composition. apply comp. apply identity. *)
  (* apply comp. eapply _map2. *)
  (* eapply composition. apply comp. apply identity. *)
  (* eapply composition. eapply inverse. apply comp_inv.  *)
  (* apply comp. eapply composition. eapply inverse. apply map_inv. *)
  (* eapply composition. *)
  (* eapply _map2. apply inv_inv. *)
  (* eapply composition. eapply _map_comp. *)
  (* apply comp. eapply _map_comp. *)
  (* apply identity. apply identity. apply identity.  *)
  (* apply identity.  *)
  admit. Defined.
Next Obligation. simpl in *. exists (inv_L _ _ _). admit. Defined.
Next Obligation. simpl in *. exists (inv _ _ _ _ [X]). admit. Defined.

Program Instance sum_weakcategory T U : WeakCategory (sum_type (T:=T) U) :=
  {| Hom1 := sum_eqHom U; Hom2 := sum_eq2Hom U |}.

Program Instance sum_weakgroupoid T U : WeakGroupoid (sum_type (T:=T) U). 
(* Next Obligation. *)
(* Proof. *)
(*   simpl in E. red in E. *)
(*   simpl in E'. red in E'. *)
(*   destruct E as [eqE eqE2], E' as [eqE' eqE'2]. *)
(*   assert(eqE = eqE'). *)
(*   apply (Trunc_2). *)
(*   subst eqE. *)
(*   apply f_equal. apply Trunc_2. *)
(* Qed. *)

(* end hide *)

Definition _Sum T (U:[T-->_Type]) := (sum_type U ; sum_weakgroupoid U). 

(** %\noindent% The proof [sum_weakgroupoid U] that we actually have a
weak groupoid makes use of the fact that [~] on [U @ t] is always
trivial to complete proofs that would have been derivable at level 2
only.

*)

Typeclasses Opaque sum_eq sum_eq2 nat_trans modification 
            Dnat_trans Dmodification Equiv_eq Equiv_eq2.
