Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.

Set Universe Polymorphism.
Set Primitive Projections.

Set Implicit Arguments.

Record sigma {A : Type} (P : A -> Type) := Build_sigma
  { proj1 : A ; proj2 : P proj1 }.

Notation " { x : T & P } " := (sigma (fun x : T => P)).

Notation "x .1" := (proj1 x) (at level 3).
Notation "x .2" := (proj2 x) (at level 3).


Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y.
  destruct p. reflexivity. Defined.



(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with eq_refl => eq_refl end.

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^-1.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y .
  destruct p. exact u. Defined. 

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Definition path_sigma {A : Type} (P : A -> Type) (u v : sigma P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v. 
  destruct u, v. simpl in *. destruct p. destruct q. reflexivity. 
Defined.
