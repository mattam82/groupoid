(* begin hide *)

Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.

Set Universe Polymorphism.
Set Program Mode.

Notation " { x : T & P } " := (sigT (fun x : T => P)).

Notation Π1 := projT1.
Notation Π2 := projT2.
Notation "[ T ]" := (Π1 T).
Notation " ( x ; p ) " := (existT _ x p).

Notation "M @ N" := ([M] N) (at level 55). 

Definition id {A : Type} (a : A) := a.

Arguments id /.

Set Implicit Arguments.
Set Primitive Projections.

(* end hide *)

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

(* begin hide *)

Instance eq_pi1 (T : OG) : OmegaGroupoid [T] := Π2 T.

(* end hide *)

Class Functor {T U : OG} (f : [T] -> [U]) := {  }.

(* begin hide *)

Definition Fun_Type (T U : OG) := {f : [T] -> [U] & Functor f}.

Infix "--->" := Fun_Type (at level 55). 

Instance fun_pi (T U : OG) (f : T ---> U) : Functor [f] := Π2 f.

Program Instance Functor_comp A B C (f : A ---> B) (g : B ---> C) : 
  Functor (λ x : [A], g @ (f @ x)).

Program Instance comp_fun : Composition Fun_Type.
Next Obligation. exact ((λ x, X0 @ (X @ x)) ; Functor_comp _ _). Defined.

Parameter funOG : ∀ T U, OmegaGroupoid (T ---> U). 

Definition _fun T U : OG := (T ---> U ; funOG _ _). 

Infix "-->" := _fun (at level 80). 

(* end hide *)

Class Equiv_struct T U (f : [T --> U]) := { }.

Definition Equiv A B := {f : A ---> B & Equiv_struct f}.

(* begin hide *)

Infix "<~>" := Equiv (at level 55). 

Instance Arrow_pi A B (f : A <~> B) : Equiv_struct [f] := Π2 f.

Instance EquivHom : HomTeq OG := {eq := Equiv}.

Instance Equiv_OmegaGroupoid : OmegaGroupoid OG.

(* end hide *)


Definition _Type : OG := (OG ; Equiv_OmegaGroupoid).


Class DependentFunctor (Γ:[_Type]) (U : [Γ --> _Type]) 
  (f : ∀ t, [U @ t]) : Type := {}.

Definition Prod_Type (T:[_Type]) (U:[T --> _Type]) :=
  {f : ∀ t, [U @ t] & DependentFunctor U f}.

(* begin hide *)

Instance Prod_pi (T:[_Type]) (U:[T --> _Type]) (f : Prod_Type U) :
  DependentFunctor U [f] := Π2 f.

Parameter prod_OG : ∀ T (U:[T --> _Type]), OmegaGroupoid (Prod_Type U). 

(* end hide *)

Definition _Prod T (U:[T --> _Type]) := (Prod_Type U ; prod_OG U). 

Definition sum_type T (U : [T --> _Type]) := {t : [T] & [U @ t]}.


(* begin hide *)

Parameter sum_OG: ∀ T U, OmegaGroupoid (sum_type (T:=T) U). 

(* end hide *)

Definition _Sum T (U:[T-->_Type]) := (sum_type U ; sum_OG U). 


Definition Hom_irr  (T : Type) : HomT T := λ _ _, unit.

Definition IrrRelOG T eq : OmegaGroupoid T := {| Hom := eq |}.


(* Takeudi-Gandi Interpretation *)

Definition Context := [_Type].

Definition Empty : [_Type] :=
  (unit; IrrRelOG {| eq := Hom_irr (T:=unit) |}).

Definition Typ (Γ:Context) := [Γ --> _Type].

Definition Elt (Γ:Context) (A:Typ Γ) := [_Prod A].

Instance TypFam_1 {Γ : Context} (A: Typ Γ) : Functor (λ s : [Γ], A @ s --> _Type : [_Type]).

Definition TypDep {Γ : Context} (A: Typ Γ) := Typ (_Sum A).

Definition TypFam {Γ : Context} (A: Typ Γ) := [_Prod (λ γ, A @ γ --> _Type; _)]. 
Next Obligation. econstructor. Defined.

Definition action {T U} :=
λ (σ: [T --> U]) (f : [U --> _Type]), (λ x, f @ (σ @ x) ; Functor_comp _ _).

(* Class Action {T} (homAc : T -> Type) := *)
(* {  WC :> OmegaGroupoid T; *)
(*    eqAc : ∀ {x}, HomT (homAc x); *)
(*    action : ∀ {x y : T}, (x ~ y) -> (homAc y) -> (homAc x)  *)
(* }. *)

Notation  "f '⋅' σ" := (action σ f) (at level 50).

Definition idTypDep (Γ:Context) : Typ Γ := (λ t, Γ; _).
Next Obligation. Admitted.

Definition idTypDep'' (Γ:Context) (σ:[Γ --> Γ]) : Typ Γ := idTypDep Γ ⋅ σ.

Instance comp_fun_depfun_1 (T T': [_Type]) (U : [T' --> _Type])
        (F : [T --> T']) (G : [_Prod U]) : DependentFunctor (U ⋅ F) (λ x : [T], G @ (F @ x)).

Definition comp_fun_depfun {T T': [_Type]} {U : [T' --> _Type]}
        (F : [T --> T']) (G : [_Prod U]) : [_Prod (U ⋅ F)] :=
(λ x : [T], G @ (F @ x); comp_fun_depfun_1 _ _).

(* end hide *)

Notation  "g '°°' f" := (comp_fun_depfun f g) (at level 50). 



Instance Curry_ {Γ: Context} {T : Typ Γ}
        (U : TypDep T) (γ : [Γ]) : Functor (λ t : [T @ γ], U @ (γ; t)).

Definition Curry {Γ: Context} {T : Typ Γ}
        (U : TypDep T) (γ : [Γ]) : [T @ γ --> _Type] :=
  (λ t : [T @ γ], U @ (γ; t) ; _). 
Next Obligation. exact (Curry_ U γ). Defined.

Instance LamT_1 {Γ: Context} {A : Typ Γ} (B: Typ (_Sum A)) :
  DependentFunctor (λ s : [Γ], [A] s --> _Type; TypFam_1 A)
                       (λ γ : [Γ], Curry B γ).

Definition LamT {Γ: Context} {A : Typ Γ} (B: TypDep A)
  : TypFam A := (λ γ, (λ t, B @ (γ; t) ; Curry_ B γ); _).
Next Obligation. exact (LamT_1 B). Defined.

(* begin hide *)

Instance SubstT_1 {Γ:Context} {A:Typ Γ} (F:TypFam A) (a:Elt A) :
 Functor (λ s, (F @ s) @ (a @ s)).
 
(* end hide *)

Instance SubExt_1 {Γ Δ : Context} {A : Typ Δ} (f: [Γ --> Δ]) (t: Elt (A ⋅ f)) : 
  Functor (λ s, (f @ s; t @ s) : [_Sum A]).

(* end hide *)

Definition SubExt {Γ Δ : Context} {A : Typ Δ} (σ: [Γ --> Δ])
  (a: Elt (A ⋅ σ)) : [Γ --> (_Sum A)] := (λ γ, (σ @ γ; a @ γ) ; _).
Next Obligation. exact (SubExt_1 _ _). Defined.

(* begin hide *)

Arguments SubExt {Γ Δ A} σ a.

Instance SubExtId_1 {Γ : Context} {A : Typ Γ} (t: Elt (A)) : 
  Functor (λ s, (s; t @ s) : [_Sum A]).

Definition SubExtId {Γ : Context} {A : Typ Γ} 
 (t: Elt A) : [Γ --> (_Sum A)] := (λ γ, (γ; t @ γ) ; _).
Next Obligation. exact (SubExtId_1 _). Defined.

Instance substF_1 {T Γ} {A:Typ Γ} (F:TypFam A) (f:[T --> Γ]) :
  DependentFunctor (λ t : [T], (A ⋅ f) @ t --> _Type; TypFam_1 (A ⋅ f)) 
                       ([F °° f] : ∀ t : [T], (A ⋅ f) @ t ---> _Type).

(* end hide *)

Instance SubWeak_1 (Γ: [_Type]) (T : [Γ --> _Type])
         : Functor (λ γt : [_Sum T], [γt]).

(* end hide *)

(* end hide *)

Definition SubWeak {Γ: Context} {T : Typ Γ} : [_Sum T --> Γ] 
  :=  (λ γt:[_Sum T], [γt] ; _).
Next Obligation. exact (SubWeak_1 T). Defined.

Notation "⇑ A" := (A ⋅ SubWeak) (at level 9, t at level 9).

Definition SubstT {Γ:Context} {A:Typ Γ} (F:TypFam A) (a:Elt A) : Typ Γ :=
  (λ γ, (F @ γ) @ (a @ γ) ; _).
Next Obligation. exact (SubstT_1 F a ). Defined.

Definition substF {T Γ} {A:Typ Γ} (F:TypFam A)
 (σ:[T --> Γ]) : TypFam (A ° σ) := ([ F °° σ] ; _).
Next Obligation. exact (substF_1 F σ). Defined.

Notation  "F '°°°' σ " := (substF F σ) (at level 50). 

Notation  "F '{{' a '}}'" := (SubstT F a) (at level 50).

(* end hide *)

(** This notion of partial substitution in a type family enables to state
 that [LamT] defines a type level $\lambda$-abstraction.

*)

Definition BetaT : forall {Δ Γ:Context}  {A:Typ Γ} (B:TypDep A)
                          (σ:[Δ --> Γ]) (a:Elt (A ⋅ σ)), 
                     LamT B °°° σ {{a}} ~ B ⋅ (SubExt σ a).
Admitted.


Instance Var_1  : forall {Γ:Context} (A:Typ Γ), 
                 DependentFunctor ⇑ A (λ t : sigT (λ t : [Γ], [[A] t]), Π2 t).

Definition Var {Γ} (A:Typ Γ) : Elt ⇑A := (λ t, Π2 t; _). 
Next Obligation. exact (Var_1 A). Defined.

(* begin hide *)

Instance Prod_1 {Γ} (A:Typ Γ) (F:TypFam A) :
  Functor (λ s : [Γ], _Prod ([F] s) : [_Type]).

(* end hide *)


Definition Prod {Γ} (A:Typ Γ) (F:TypFam A) : Typ Γ :=
  (λ s, _Prod (F @ s); _).
Next Obligation. exact (Prod_1 A F). Defined.

(* begin hide *)

Instance App_1 {Γ} {A:Typ Γ} {F:TypFam A} (c:Elt (Prod F)) (a:Elt A) :
  DependentFunctor (F {{a}}) (λ s : [Γ], [[c] s] ([a] s)).
 
(* end hide *)

Definition App {Γ} {A:Typ Γ} {F:TypFam A}
  (c:Elt (Prod F)) (a:Elt A) : Elt (F {{a}}) :=
  (λ s, (c @ s) @ (a @ s); _).
Next Obligation. exact (App_1 c a). Defined.

(* begin hide *)

Notation "M '@@' N" := (App M N) (at level 50).

Instance Lam_1 {Γ} {A:Typ Γ} {F:TypDep A}
  (b:Elt F) (γ:[Γ]) :
  DependentFunctor ([LamT F] γ) (fun t => b @ (γ ; t)).

Definition Lam_partial {Γ} {A:Typ Γ} {F:TypDep A}
  (b:Elt F) (γ:[Γ]) : [Prod (LamT F) @ γ] :=
 (λ t, b @ (γ ; t) ; _). 
Next Obligation. exact (Lam_1 _ _). Defined.

Instance Lam_2 {Γ} {A:Typ Γ} {B:TypDep A} (b:Elt B) :
 DependentFunctor (Prod (LamT B)) (Lam_partial b).


Definition Lam {Γ} {A:Typ Γ} {B:TypDep A} (b:Elt B) :
  Elt (Prod (LamT B)) := (λ γ, (λ t, b @ (γ ; t) ; _); _).
Next Obligation. exact (Lam_1 _ _). Defined.
Next Obligation. exact (Lam_2 _). Defined.



Lemma Beta {Γ} {A:Typ Γ} {F:TypDep A} (b:Elt F) (a:Elt A) : 
  [Lam b @@ a] = [b °° SubExtId a].
reflexivity.
Defined.

Definition prod_eq (A: [_Type]) (T U : [A --> _Type]) 
        (e:T ~ U) : [_Prod T --> _Prod U]. Admitted.

Notation "e 'with' t" := (prod_eq t @ e) (at level 50).

Instance cst_type_1 (T:[_Type]) (Γ: Context) : Functor (λ _ : [Γ], T).


Definition non_dep_type {Γ} T : Typ Γ := (λ γ, T; _).
Next Obligation. exact (cst_type_1 _ _). Defined.



Definition Propositions := { P : Prop & unit }.



Definition _Prop : OG  := 
  (Propositions; IrrRelOG {| eq := (λ P Q, [P] <-> [Q]) |}).



Lemma eq_Prod_ctxt {T Γ} (A:Typ Γ) (F:TypFam A) (f: [T --> Γ]) :
  Prod F ⋅ f ~ Prod (F °°° f).
Admitted.

Notation "↑ t" := (t °° SubWeak with eq_Prod_ctxt _ _) (at level 9, t at level 9).
 

Definition Conversion_Eq (Γ: Context) (A B: Typ Γ) 
        (t : Elt A) (e : A = B) : Elt B.
Proof. destruct e. exact t. Defined.


Definition Heq_rect Γ (A B: Typ Γ) (e : A ~ B) : 
  Elt A -> Elt B.
Admitted.
