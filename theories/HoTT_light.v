Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.

Set Standard Proposition Elimination Names.
Set Universe Polymorphism.
Set Primitive Projections.

Set Implicit Arguments.

Section TypeEq.
  Local Definition T := Type.
  Inductive equality (A : T) : A -> A -> T :=
  | eq_refl a : equality a a.

  Lemma eq_sym (A : T) (x y : A) : equality x y -> equality y x.
  Proof.
    intros []. apply eq_refl.
  Defined.

  Lemma eq_trans (A : T) (x y z : A) : equality x y -> equality y z -> equality x z.
  Proof.
    intros []. intros a []. apply eq_refl.
  Defined.

End TypeEq.

Notation " x = y " := (@equality _ x y).
Notation " x = y " := (@equality _ x y) : type_scope.

Record sigma {A : Type} (P : A -> Type) := Build_sigma
  { proj1 : A ; proj2 : P proj1 }.

Notation " { x : T & P } " := (sigma (fun x : T => P)).

Notation " ( x ; p ) " := (@Build_sigma _ _ x p).

Notation "x .1" := (proj1 x) (at level 3).
Notation "x .2" := (proj2 x) (at level 3).


Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y.
  destruct p. constructor. 
Defined.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Notation "f ^^-1" := (@equiv_inv _ _ f _) (at level 3).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with eq_refl _ => eq_refl _ end.

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Axiom funext : Funext.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^^-1.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y .
  destruct p. exact u. Defined. 

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Definition path_sigma {A : Type} (P : A -> Type) (u v : sigma P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v. 
  destruct u, v. simpl in *.
  destruct p. simpl in q. destruct q. apply eq_refl.
Defined.

Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z')): (z = z').
  destruct pq. destruct z, z'. simpl in *. destruct X, X0. apply eq_refl.
Defined.

Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
  : IsEquiv (path_prod_uncurried z z') | 0.
Admitted.

Class Contr (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Global Instance contr_forall A {P : A -> Type} {H : forall a, Contr (P a)}
  : Contr (forall a, P a) | 100.
Proof.
  exists (fun a => @center _ (H a)).
  intro f.  apply path_forall.  intro a.  apply contr.
Defined.


Definition concat A (x y z : A) (e : x = y) (e' : y = z) : x = z.
destruct e. exact e'. Defined.

Infix "@@" := concat (at level 50).

Definition moveR_E A B (f:A -> B) {H : IsEquiv f} (x : A) (y : B) (p : x = f^^-1 y)
  : (f x = y)
  := ap f p @@ (@eisretr _ _ f _ y).

Lemma contr_equiv A B (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (center A)).
  intro y.
  eapply moveR_E.
  apply contr.
Qed.

Program Instance isequiv_inverse A B (f:A -> B) (H:IsEquiv f) : IsEquiv (f^^-1) | 1000
    := BuildIsEquiv (@eissect _ _ f _) (@eisretr _ _ f _) _.
Next Obligation. admit. Defined. 

Definition contr_sigma A {P : A -> Type}
  {H : Contr A} `{H0 : forall a, Contr (P a)}
  : Contr (sigma P).
Proof.
  exists (center A; center (P (center A))).
  intros [a ?].
  (* refine (path_sigma P (contr a) (path_contr _ _)). *)
Admitted.

Definition path_sigma_uncurried (A : Type) (P : A -> Type) (u v : sigma P)
  (pq : sigma (fun p => p # u.2 = v.2))
  : u = v.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p. simpl in *. destruct q.
  apply eq_refl.
Defined.

Definition path_sigma_equiv {A : Type} (P : A -> Type) (u v : sigma P):
           IsEquiv (path_sigma_uncurried u v).
Admitted.

Instance contr_unit : Contr unit | 0 := let x := {|
  center := tt;
  contr := fun t : unit => match t with tt => eq_refl _ end
|} in x.

Definition path_contr A {H:Contr A} (x y : A) : x = y
  := concat (eq_sym (@contr _ H x)) (@contr _ H y).

Definition path2_contr A {H:Contr A} {x y : A} (p q : x = y) : p = q.
Admitted.

Instance contr_paths_contr A {H:Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := concat (eq_sym (contr x)) (contr y);
  contr := path2_contr (concat (eq_sym (contr x)) (contr y))
|} in c.

Program Instance contr_prod A B {CA : Contr A} {CB : Contr B} : Contr (prod A B).
Next Obligation. exact (@center _ CA, @center _ CB). Defined.
Next Obligation. apply path_prod; apply contr. Defined.
