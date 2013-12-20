Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.

Set Universe Polymorphism.
Set Program Mode.
Set Primitive Projections.

Set Implicit Arguments.
Unset Strict Implicit.

Record sigma {A : Type} (P : A -> Type) := buildsigma
  { proj1 : A ; proj2 : P proj1 }.

Notation " { x : T & P } " := (sigma (fun x : T => P)).

Notation "x .1" := (proj1 x) (at level 3).
Notation "x .2" := (proj2 x) (at level 3).

Notation " ( x ; p ) " := (buildsigma (proj1:=x) p).

Notation Π1 := proj1.
Notation Π2 := proj2.
Notation "[ T ]" := (Π1 T).

Notation "M @ N" := ([M] N) (at level 55). 

Definition id {A : Type} (a : A) := a.

Arguments id /.

Set Implicit Arguments.
Set Primitive Projections.

Definition HomT (T : Type) := T -> T -> Type.

Class HomTeq T := { eq : HomT T }.

Infix "~" := eq (at level 80). 

Class Composition {A} (Hom : HomT A) :=
  composition : ∀ {x y z:A}, Hom x y -> Hom y z -> Hom x z.

Notation  "g ° f" := (composition f g) (at level 50).

Class OmegaGroupoid T : Type := {
  Hom :> HomTeq T 
}.

Definition OG := {T:Type & OmegaGroupoid T}.

Instance eq_pi1 (T : OG) : OmegaGroupoid [T] := Π2 T.

Class Functor {T U : OG} (f : [T] -> [U]) := {  }.

Definition Fun_Type (T U : OG) := {f : [T] -> [U] & Functor f}.

Infix "--->" := Fun_Type (at level 55). 

Instance fun_pi (T U : OG) (f : T ---> U) : Functor [f] := Π2 f.

Parameter Hom_Functor : forall T U, HomT (T ---> U).

Instance HomTeq_Functor T U : HomTeq (T ---> U) := {| eq := Hom_Functor (T:=T) (U:=U)|}. 

Instance Functor_comp A B C (f : A ---> B) (g : B ---> C) : 
  Functor (λ x : [A], g @ (f @ x)).

Program Instance comp_fun : Composition Fun_Type.
Next Obligation. exact ((λ x, X0 @ (X @ x)) ; Functor_comp _ _). Defined.

Parameter funOG : ∀ T U, OmegaGroupoid (T ---> U). 

Definition _fun T U : OG := (T ---> U ; funOG _ _). 

Infix "-->" := _fun (at level 80). 



Class Equiv_struct T U (f : [T --> U]) := { }.

Definition Equiv A B := {f : A ---> B & Equiv_struct f}.



Infix "<~>" := Equiv (at level 55). 

Instance Arrow_pi A B (f : A <~> B) : Equiv_struct [f] := Π2 f.

Instance EquivHom : HomTeq OG := {eq := Equiv}.

Instance Equiv_OmegaGroupoid : OmegaGroupoid OG.




Definition _Type : OG := (OG ; Equiv_OmegaGroupoid).


Class DependentFunctor (Γ:[_Type]) (U : [Γ --> _Type]) 
  (f : ∀ t, [U @ t]) : Type := {}.

Definition Prod_Type (T:[_Type]) (U:[T --> _Type]) :=
  {f : ∀ t, [U @ t] & DependentFunctor f}.


Instance Prod_pi (T:[_Type]) (U:[T --> _Type]) (f : Prod_Type U) :
  DependentFunctor [f] := Π2 f.

Parameter prod_OG : ∀ T (U:[T --> _Type]), OmegaGroupoid (Prod_Type U). 



Definition _Prod T (U:[T --> _Type]) := (Prod_Type U ; prod_OG U). 

Definition sum_type T (U : [T --> _Type]) := {t : [T] & [U @ t]}.




Parameter sum_OG: ∀ T U, OmegaGroupoid (sum_type (T:=T) U). 



Definition _Sum T (U:[T-->_Type]) := (sum_type U ; sum_OG U). 


Definition Hom_irr  (T : Type) : HomT T := λ _ _, unit.

Definition IrrRelOG T eq : OmegaGroupoid T := {| Hom := eq |}.


(* Takeuti-Gandy Interpretation *)

Definition Context := [_Type].

Definition Empty_Ctx : Context :=
  (unit; IrrRelOG {| eq := Hom_irr (T:=unit) |}).

Definition Typ (Γ:Context) := [Γ --> _Type].

Definition Elt (Γ:Context) (T:Typ Γ) := [_Prod T].

Definition TypDep {Γ : Context} (T: Typ Γ) := Typ (_Sum T).

Instance TypFam_1 {Γ : Context} (T: Typ Γ) : Functor (λ γ : [Γ], T @ γ --> _Type : [_Type]).

Definition TypFam {Γ : Context} (T: Typ Γ) := [_Prod (λ γ : [Γ], T @ γ --> _Type; TypFam_1 _)].

Definition substitution Γ Δ := [Γ --> Δ].

Notation  "Γ '⇀' Δ" := (substitution Γ Δ) (at level 50).

Definition action {Γ Δ} := λ (σ: Γ ⇀ Δ) (T : Typ Δ), (λ x, T @ (σ @ x) ; Functor_comp _ _).

Notation  "T '⋅' σ" := (action σ T) (at level 50).

Instance composition_subst_Typ_1 (Γ Δ: Context) (T : Typ Δ)
        (σ : Γ ⇀ Δ) (t : Elt T) : DependentFunctor (U:=T ⋅ σ) (λ x : [Γ], t @ (σ @ x)).

Definition composition_subst_Typ {Γ Δ: Context} {T : Typ Δ}
        (σ : Γ ⇀ Δ) (t : Elt T) : Elt (T ⋅ σ) := 
  (λ x : [Γ], t @ (σ @ x); composition_subst_Typ_1 _ _).

Notation  "t '{{{' σ '}}}'" := (composition_subst_Typ σ t) (at level 50). 

Instance Curry_ {Γ: Context} {T : Typ Γ}
        (U : TypDep T) (γ : [Γ]) : Functor (λ t : [T @ γ], U @ (γ; t)).

Definition Curry {Γ: Context} {T : Typ Γ}
        (U : TypDep T) (γ : [Γ]) : [T @ γ --> _Type] :=
  (λ t : [T @ γ], U @ (γ; t) ; _). 
Next Obligation. exact (Curry_ U γ). Defined.

Instance LamT_1 {Γ: Context} {T : Typ Γ} (U: TypDep T) :
  DependentFunctor (U := (λ γ : [Γ], [T] γ --> _Type; TypFam_1 T))
                   (λ γ : [Γ], Curry U γ).

Definition LamT {Γ: Context} {T : Typ Γ} (U: TypDep T) : TypFam T 
  := (λ γ, (λ t, U @ (γ; t) ; Curry_ U γ); _).
Next Obligation. exact (LamT_1 U). Defined.

Instance SubExt_1 {Γ Δ : Context} {T : Typ Δ} (σ: Γ ⇀ Δ) (t: Elt (T ⋅ σ)) : 
  Functor (λ γ, (σ @ γ; t @ γ) : [_Sum T]).

Definition SubExt {Γ Δ : Context} {T : Typ Δ} (σ: Γ ⇀ Δ) (t: Elt (T ⋅ σ)) : Γ ⇀ _Sum T 
  := (λ γ, (σ @ γ; t @ γ) ; _).
Next Obligation. exact (SubExt_1 _ _). Defined.

Arguments SubExt {Γ Δ T} σ t.

Instance SubExtId_1 {Γ : Context} {T : Typ Γ} (t: Elt T) : 
  Functor (λ γ, (γ; t @ γ) : [_Sum T]).

Definition SubExtId {Γ : Context} {T : Typ Γ} 
 (t: Elt T) : Γ ⇀ _Sum T := (λ γ, (γ; t @ γ) ; SubExtId_1 _). 

Instance substF_1 {Γ Δ} {T:Typ Δ} (F:TypFam T) (σ : Γ ⇀ Δ) :
  DependentFunctor (U:=(λ t : [Γ], (T ⋅ σ) @ t --> _Type; TypFam_1 (T ⋅ σ)))
                   ([F {{{σ}}}] : ∀ t : [Γ], (T ⋅ σ) @ t ---> _Type).

Instance SubWeak_1 Γ (T : Typ Γ)
         : Functor (λ γt : [_Sum T], [γt]).

Definition SubWeak {Γ} {T : Typ Γ} : _Sum T ⇀ Γ 
  :=  (λ γt:[_Sum T], [γt] ; SubWeak_1 T).

Notation "⇑ T" := (T ⋅ SubWeak) (at level 9, t at level 9).


Instance SubstT_1 {Γ} {T:Typ Γ} (F:TypFam T) (a:Elt T) :
 Functor (λ s, (F @ s) @ (a @ s)).
 
Definition SubstT {Γ} {T:Typ Γ} (F:TypFam T) (t:Elt T) : Typ Γ :=
  (λ γ, (F @ γ) @ (t @ γ) ; SubstT_1 F t).

Definition substF {Γ Δ} {T:Typ Δ} (F:TypFam T)
 (σ : Γ ⇀ Δ) : TypFam (T ° σ) := ([ F {{{σ}}}] ; substF_1 F σ).

Notation  "F '°°' σ " := (substF F σ) (at level 50). 

Notation  "F '{{' a '}}'" := (SubstT F a) (at level 50).



(** This notion of partial substitution in a type family enables to state
 that [LamT] defines a type level $\lambda$-abstraction.

*)

Definition BetaT : forall {Γ Δ} {T:Typ Δ} (U:TypDep T)
                          (σ : Γ ⇀ Δ) (t:Elt (T ⋅ σ)), 
                     LamT U °° σ {{t}} ~ U ⋅ (SubExt σ t).
Admitted. (* should be reflexivity *)

Instance Var_1  : forall {Γ:Context} (T:Typ Γ), 
                 DependentFunctor (U:=⇑ T) (λ t : sigma (λ γ, [T @ γ]), Π2 t).

Definition Var {Γ} (T:Typ Γ) : Elt ⇑T := (λ t, Π2 t; Var_1 T).


Instance Prod_1 {Γ} (T:Typ Γ) (F:TypFam T) :
  Functor (λ γ : [Γ], _Prod ([F] γ) : [_Type]).


Definition Prod {Γ} (T:Typ Γ) (F:TypFam T) : Typ Γ :=
  (λ γ, _Prod (F @ γ); Prod_1 T F). 


Instance App_1 {Γ} {T:Typ Γ} {F:TypFam T} (P : Elt (Prod F)) (t:Elt T) :
  DependentFunctor (U := F {{t}}) (λ γ, (P @ γ) @ (t @ γ)).
 
Definition App {Γ} {T:Typ Γ} {F:TypFam T}
  (P : Elt (Prod F)) (t:Elt T) : Elt (F {{t}}) :=
  (λ γ, (P @ γ) @ (t @ γ); App_1 _ _).

Notation "M '@@' N" := (App M N) (at level 50).

Instance Lam_1 {Γ} {T:Typ Γ} {U:TypDep T} (P:Elt U) (γ:[Γ]) :
  DependentFunctor (U := (LamT U) @ γ) (fun t => P @ (γ ; t)).

Definition Lam_partial {Γ} {T:Typ Γ} {U:TypDep T}
  (P:Elt U) (γ:[Γ]) : [Prod (LamT U) @ γ] :=
 (λ t, P @ (γ ; t) ; Lam_1 _ _). 

Instance Lam_2 {Γ} {T:Typ Γ} {U:TypDep T} (P:Elt U) :
 DependentFunctor (U := Prod (LamT U)) (Lam_partial P).

Definition Lam {Γ} {T:Typ Γ} {U:TypDep T} (P:Elt U) :
  Elt (Prod (LamT U)) := (λ γ, (λ t, P @ (γ ; t) ; _); _).
Next Obligation. exact (Lam_1 _ _). Defined.
Next Obligation. exact (Lam_2 _). Defined.


Definition Beta {Γ} {T:Typ Γ} {U:TypDep T} (P:Elt U) (t:Elt T) : 
  [Lam P @@ t] = [P {{{ SubExtId t }}}] := eq_refl.

Definition prod_eq Γ (T U : Typ Γ) 
        (e:T ~ U) : [_Prod T --> _Prod U]. Admitted.

Notation "e 'with' t" := (prod_eq t @ e) (at level 50).

Instance non_dep_type_1 (T:[_Type]) (Γ: Context) : Functor (λ _ : [Γ], T).

Definition non_dep_type {Γ} T : Typ Γ := (λ γ, T; non_dep_type_1 _ _).


Definition Propositions := { P : Prop & unit }.

Definition _Prop : OG  := 
  (Propositions; IrrRelOG {| eq := (λ P Q, [P] <-> [Q]) |}).

Definition eq_Prod_ctxt {Γ Δ} (T:Typ Δ) (F:TypFam T) (σ : Γ ⇀ Δ) : 
  @eq _ (HomTeq_Functor _ _) (Prod F ⋅ σ) (Prod (F °° σ)).
Admitted.

Notation "↑ t" := (t °° SubWeak with eq_Prod_ctxt _ _) (at level 9, t at level 9).

(* We miss coherences to define this one   *)
 
Definition Heq_rect Γ (T U: Typ Γ) (e : T ~ U) : 
  Elt T -> Elt U.
Admitted.