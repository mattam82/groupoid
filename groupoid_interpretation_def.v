(** printing ~1 $\sim_1$ *)
(** printing ~ $\sim_2$ *)
(** printing ~2 $\sim_2$ *)
(** printing Π1 $\pi_1$*)
(** printing Π2 $\pi_2$*)
(** printing Πi $\pi_i$*)
(** printing --> $\longrightarrow$*)
(** printing ---> $\longrightarrow$*)
(** printing β $\beta$*)
(** printing γ $\gamma$*)
(** printing Γ $\Gamma$*)
(** printing γt $\gamma t$*)
(** printing Δ $\Delta$*)
(** printing χ $\chi$*)
(** printing [! $\llbracket$*)
(** printing !] $\rrbracket$*)
(** printing |- $\vdash$*)
(** printing === $\equiv$*)
(** printing @ $\star$*)
(** printing ° $\circ$*)
(** printing °° $\circ \circ$*)
(** printing °°° $\circ \circ \circ$*)
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


(* begin hide *)

Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Require Import Setoid.
Add Rec LoadPath ".".
Require Import groupoid.
Require Import groupoid_utility.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Program Mode.
 
Opaque Equiv_adjoint.
Opaque map_id map_inv Dmap_id.

(* end hide *)

(** 

  The interpretation is based on the Takeuti-Gandy interpretation of simple type theory, 
  recently generalized to dependent type theory in %\cite{barras:_gener_takeut_gandy_inter}% using 
  Kan semisimplicial sets.
  There are two main novelties in our interpretation. First, we take advantage of universe polymorphism 
  to interpret dependent types directly as weak functors into [_Type]. This provides a uniform interpretation
  that lift to higher-dimensional weak groupoids, and ultimately to $\omega$-groupoids.
  Second, we provide an interpretation in a model where structures that are definitionally equal for
  Kan semisimplicial sets are only homotopically equal, which requires more care in the definitions
  (see for instance the definition of [Lam] in Section %\ref{sec:interp}% which mixes two points 
   of view on fibrations). 

  We only present the computational part of the interpretation, the proofs of functoriality and naturality 
  are not detailled but most of them are available in the %\Coq% development. We have admitted
  some of these administrative compatibility lemmas.


  ** Dependent types

  The judgment context $\Gamma \vdash$ of Section
  %\ref{sec:proof-assistant}% is represented in %\Coq% as a weak
  groupoid, noted [Context := [_Type]]. The empty context is
  interpreted as the weak groupoid with exactly one element at each
  dimension.  Types in a context [Γ], noted [Typ Γ], are weak
  (context) functors from [Γ] to weak groupoids.  Thus, a judgment
  $\Gamma \vdash A : s$ is represented as a term [A] of type [Typ
  Γ]. Context extension is given by dependent sums, i.e., the judgment
  $\Gamma, x:A \vdash$ is represented as [_Sum A]. 

*)

(* begin hide *)

Unset Implicit Arguments.

Definition Hom_irr (T : Type) : HomT T := λ _ _, unit.

Set Implicit Arguments.

Program Definition _Hom_irr T (Hom : HomT1 T) : HomT2 eq1 := {| eq2 := fun x y => Hom_irr _ |}.

Obligation Tactic := intros; constructor; intros; exact tt.

Program Instance IrrRelEquiv T : Equivalence (Hom_irr T).
Program Instance IrrRelCat T (Hom : HomT1 T) (id : Identity eq1) (comp : Composition eq1): CategoryP (_Hom_irr Hom).

Program Instance IrrRelGrp T (Hom : HomT1 T) (id : Identity eq1) (comp : Composition eq1) (inv : Inverse eq1): GroupoidP (IrrRelCat T Hom id comp).

Program Instance IrrRelId T (Hom : HomT1 T) (x y : T) : Identity (Hom_irr (x ~1 y)).

Program Instance IrrRelComp T (Hom : HomT1 T) (x y : T) : Composition (Hom_irr (x ~1 y)).

Program Instance IrrRelInverse T (Hom : HomT T) (x y : T) : Inverse (Hom_irr (Hom x y)).

Program Instance IrrRelEq T (Hom : HomT T) (x y : T) : Equivalence (Hom_irr (Hom x y)). 

Program Definition IrrRelWeakCategory T (Hom : HomT1 T) (id : Identity eq1) (comp : Composition eq1) : WeakCategory T:=  {| Hom2 := _Hom_irr Hom; Category_1 := IrrRelCat T Hom id comp ; Equivalence_2 := IrrRelEq eq1 |}.

Program Definition IrrRelWeakGroupoid T (Hom : HomT1 T) (id : Identity eq1) (comp : Composition eq1) (inv : Inverse eq1) : WeakGroupoid T := 
  {| WC := IrrRelWeakCategory id comp ; G := IrrRelGrp T Hom id comp inv|}.

Arguments IrrRelWeakGroupoid {T} Hom {id comp inv}.

(* end hide *)

Obligation Tactic := simpl; intros.
Definition Context := [_Type].

Definition Empty : [_Type] := 
  (unit; IrrRelWeakGroupoid {| eq1 := Hom_irr unit |}).

Definition Typ (Γ:Context) := [Γ --> _Type].

Definition Elt (Γ:Context) (A:Typ Γ) := [_Prod A].

Instance TypFam_1 {Γ : Context} (A: Typ Γ) :WeakFunctor (λ s : [Γ], A @ s --> _Type : [_Type]).
Next Obligation. apply fun_eqT. apply (map A X). apply identity. Defined.
Next Obligation. exists (fun_eq_map _ _ _ _ e e'). apply AllEquivEq. Defined.
Next Obligation. unfold TypFam_1_obligation_1. 
                 exists (fun_eq_eq (map2 A X) (identity (identity _Type))).
                 apply AllEquivEq.
Defined.


Definition TypDep {Γ : Context} (A: Typ Γ) := Typ (_Sum A).

(* end hide *)
(** Elements of [A] introduced by a sequent $\Gamma \vdash x:A$ are weak
  dependent (context) functors from [Γ] to [A] that returns for each
  context valuation [γ], an object of [A @ γ] respecting equality of contexts.
  The type of elements of [A] is noted [Elt A := [_Prod A]] (context is implicit).
*)


(**

  A dependent type $\Gamma, x:A \vdash B$ is interpreted in two
  equivalent ways: simply as a type [TypDep A := Typ (_Sum A)] on the
  dependent sum of [Γ] and [A] or as a type family [TypFam A] over [A]
  (corresponding to a family of sets in constructive mathematics). A
  type family can be seen as a fibration (or bundle) from [B] to [A].

*)

Definition TypFam {Γ : Context} (A: Typ Γ) := 
  [_Prod (λ γ, A @ γ --> _Type; _)]. 

Class Action {T} (homAc : T -> Type) :=
{  WC :> WeakCategory T;
   eqAc : ∀ {x}, HomT (homAc x);
   action : ∀ {x y : T}, (x ~1 y) -> (homAc y) -> (homAc x) ;
   idAc : ∀ {x} (f : homAc x), eqAc (action (identity x) f) f ;
   assocAc : ∀ {x y z} (σ: x ~1 y) (τ: y ~1 z) (f: homAc z),
            eqAc (action (τ ° σ) f) (action σ (action τ f))
}.

Notation  "f '⋅' σ" := (action σ f) (at level 50).

Instance ActionType : Action (T:=[_Type]) (fun T => T ---> _Type) :=
  {| WC := WeakCategory_fun ; eqAc := λ T, nat_trans (T:=T) (U:=_Type) ;
     action := λ T U (σ: [T --> U]) (f : [U --> _Type]), (λ x, f @ (σ @ x) ; arrow_comp _ _ _ _ _) |}.
Next Obligation. exists (λ t , identity _). econstructor. intros.
                 eapply composition. apply equiv_id_L. eapply inverse. apply equiv_id_R. Defined.
Next Obligation. exists (λ t , identity _).  econstructor. intros.
                 eapply composition. apply equiv_id_L. eapply inverse. apply equiv_id_R. Defined.

Definition idTypDep (Γ:Context) : Typ Γ := (λ t, Γ; _).  

Definition idTypDep'' (Γ:Context) (σ:[Γ --> Γ]) : Typ Γ := idTypDep Γ ⋅ σ.

