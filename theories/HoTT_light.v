Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics Setoid.

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
    intros [] []. apply eq_refl.
  Defined.

End TypeEq.

Arguments equality {A} _ _.
Arguments eq_refl {A} [a].

Require Import CRelationClasses CMorphisms.

Instance eq_reflexive A : Reflexive (@equality A).
Proof. exact (@eq_refl A). Defined.

Instance eq_symmetric A : Symmetric (@equality A).
Proof. exact (@eq_sym A). Defined.

Instance eq_transitive A : Transitive (@equality A).
Proof. exact (@eq_trans A). Defined.

Notation " x = y " := (@equality _ x y).
Notation " x = y " := (@equality _ x y) : type_scope.

Inductive prod (A B : Type) := pair : A -> B -> prod A B.

Notation " X * Y " := (prod X Y) : type_scope.
Notation " ( x , p ) " := (@pair _ _ x p).

Definition fst {A B} (p : A * B) : A := match p with pair a b => a end.
Definition snd {A B} (p : A * B) : B := match p with pair a b => b end.

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

(** A typeclass that includes the data making [f] into an adjoin equivalence*)

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
  := fun x => match h with eq_refl => eq_refl end.

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

(* Axiom funext : Funext. *)

(*
Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^^-1.
 *)

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
  destruct pq. destruct z, z'. simpl in *. destruct e , e0. reflexivity. 
Defined.

Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (pair p q).

Definition eta_path_prod {A B : Type} {z z' : A * B} (p : z = z') :
  path_prod _ _(ap fst p) (ap snd p) = p.
  destruct p, a. reflexivity.
Defined.

Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (pair x y) (pair x' y') p q.

Definition ap_fst_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap fst (path_prod _ _ p q) = p.
Proof.
  destruct z, z'. simpl in *. destruct p, q.
  apply eq_refl.
Defined.

Definition ap_snd_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap snd (path_prod _ _ p q) = q.
Proof.
  destruct z, z'; simpl in *. destruct p, q.
  apply eq_refl.
Defined. 

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
: IsEquiv (path_prod_uncurried z z').
Proof.
  refine (BuildIsEquiv _ _ _).
  - exact (fun r => (ap fst r, ap snd r)).
  - intro; apply eta_path_prod.
  - intros [p q]. exact (path_prod'
                          (ap_fst_path_prod p q)
                          (ap_snd_path_prod p q)). 
  - destruct z as [x y], z' as [x' y'].
    intros [p q]; simpl in p, q.
    destruct p, q; apply eq_refl.
Defined.

Class Contr (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

(*
Global Instance contr_forall A {P : A -> Type} {H : forall a, Contr (P a)}
  : Contr (forall a, P a) | 100.
Proof.
  exists (fun a => @center _ (H a)).
  intro f.  apply path_forall.  intro a.  apply contr.
Defined.
*)

Definition concat A (x y z : A) (e : x = y) (e' : y = z) : x = z.
destruct e. exact e'. Defined.

Infix "@@" := concat (at level 50).

Definition moveR_E A B (f:A -> B) {H : IsEquiv f} (x : A) (y : B) (p : x = f^^-1 y)
  : (f x = y)
  := ap f p @@ (@eisretr _ _ f _ y).


Lemma contr_equiv A B (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (@center _ H0)). 
  intro y.
  eapply moveR_E.
  apply contr.
Qed.
 
Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  eq_refl @@ p = p.
  apply eq_refl.
Defined. 

Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @@ eq_refl  = p.
  destruct p. apply eq_refl. 
Defined.

Definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  eq_sym p @@ p = eq_refl. 
  destruct p. apply eq_refl.
Defined. 

Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @@ eq_sym p = eq_refl.
  destruct p; apply eq_refl.
Defined.

Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @@ (q @@ r) = (p @@ q) @@ r.
  destruct p, q; apply eq_refl.
Defined.

Instance equality_equiv A :
  Equivalence (@equality A) := {}.

Instance concat_morphism (A : Type@{i}) x y z :
  Proper@{i i} (equality ==> equality ==> equality) (@concat A x y z).
Proof. reduce. destruct x0. destruct X. destruct x1. destruct X0. reflexivity. Defined.

Instance trans_co_eq_inv_arrow_morphism :
  ∀ (A : Type@{i}) (R : crelation@{i i} A),
    Transitive R → Proper (R ==> respectful equality (flip arrow)) R.
Proof. reduce. transitivity y. assumption. now destruct X1. Defined.

Definition concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
    (r @@ p x) @@ ap g q = (r @@ q) @@ p y.
  destruct q. simpl.
  destruct (concat_p1 r).
  apply concat_p1.
Defined.

Definition whiskerL {A : Type} {x y z : A} (p : x = y)
           {q r : y = z} (h : q = r) : p @@ q = p @@ r.
  destruct p. exact h.
Defined.

Definition whiskerR {A : Type} {x y z : A} {p q : x = y}
           (h : p = q) (r : y = z) : p @@ r = q @@ r.
  destruct p, h. apply eq_refl.
Defined. 

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  eq_sym q @@ p = eq_refl -> p = q. 
  destruct q. trivial.
Defined.

Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
: eq_sym p = eq_sym q := ap (@eq_sym _ _ _) h.

Definition ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q.
  destruct r; apply eq_refl.
Defined. 

Definition ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @@ (ap f (p @@ q)) = (r @@ ap f p) @@ (ap f q).
Proof.
  destruct p, q. simpl. exact (concat_p_pp r (eq_refl) (eq_refl)).
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun x => g (f x)) p = ap g (ap f p).
  destruct p. apply eq_refl.
Defined.

Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @@ (p y) = (p x) @@ q.
  destruct q; simpl; destruct (p a). reflexivity.
Defined.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @@ q) = (ap f p) @@ (ap f q).
  destruct p, q. apply eq_refl.
Defined.

Definition concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @@ q) @@ eq_sym q = p.
  destruct p, q; apply eq_refl.
Defined.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (eq_sym p) = eq_sym (ap f p).
  destruct p. apply eq_refl.
Defined.

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @@ (ap f q) =  q @@ (p y).
  destruct q. apply concat_p1.
Defined.

Definition concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @@ (eq_sym p @@ q) = q.
  destruct p. apply eq_refl.
Defined.

Definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @@ eq_sym q) @@ q = p.
  destruct p, q. apply eq_refl.
Defined.

Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
    (r @@ ap f q) @@ p y = (r @@ p x) @@ q.
  destruct q; simpl. destruct (concat_p1 r). apply eq_sym, concat_p1. 
Defined.

Definition ap_p {A B : Type} (f : A -> B) {x y : A} (p q: x = y) (e : p = q) :
  ap f p = ap f q.
  destruct e. apply eq_refl.
Defined.

Instance ap_morphism (A : Type@{i}) (B : Type@{j}) x y f :
  Proper (@equality (@equality A x y) ==> @equality (@equality B (f x) (f y))) (@ap A B f x y).
Proof. reduce. destruct x0. destruct X. reflexivity. Defined.

Instance reflexive_proper_proxy :
  ∀ (A : Type@{i}) (R : crelation@{i i} A), Reflexive R → ∀ x : A, ProperProxy R x.
Proof. intros. reduce. apply X. Defined.

Definition isequiv_inverse' A B (f:A -> B) (H:IsEquiv f) : IsEquiv (f^^-1) .
Proof.
  refine (BuildIsEquiv (@eissect _ _ f _) (@eisretr _ _ f _) _).
  intros b.
  rewrite <- (concat_1p (eissect _)).
  rewrite <- (concat_Vp  (ap f^^-1 (eisretr (f (f^^-1 b))))).
  rewrite (whiskerR (inverse2 (ap02 f^^-1 (eisadj (f^^-1 b)))) _).
  refine (whiskerL _ (eq_sym (concat_1p (eissect _))) @@ _).
  rewrite <- (concat_Vp (eissect (f^^-1 (f (f^^-1 b))))).
  rewrite <- (whiskerL _ (concat_1p (eissect (f^^-1 (f (f^^-1 b)))))).
  rewrite <- (concat_pV (ap f^^-1 (eisretr (f (f^^-1 b))))).
  apply moveL_M1.
  repeat rewrite concat_p_pp.
    (* Now we apply lots of naturality and cancel things. *)
  rewrite <- (concat_pp_A1 (fun a => eq_sym (eissect a)) _ _).
  rewrite (ap_compose f f^^-1).
    rewrite <- (ap_p_pp _ _ (ap f (ap f^^-1 (eisretr (f (f^^-1 b))))) _).
  rewrite <- (ap_compose f^^-1 f).
  rewrite (concat_A1p (@eisretr _ _ f _) _).
  rewrite ap_pp, concat_p_pp.
  rewrite (concat_pp_V _ (ap f^^-1 (eisretr (f (f^^-1 b))))).
  repeat rewrite <- ap_V. rewrite <- ap_pp.
  rewrite <- (concat_pA1 (fun y => eq_sym (eissect y)) _).
  rewrite ap_compose, <- (ap_compose f^^-1 f).
  rewrite <- ap_p_pp.
  rewrite (concat_A1p (@eisretr _ _ f _) _).
  rewrite concat_p_Vp.
  rewrite <- ap_compose.
  rewrite (concat_pA1_p (@eissect _ _ f _) _).
  rewrite concat_pV_p; apply concat_Vp.
Defined.

(* raise down the number of universes *)

Definition isequiv_inverse A B f H := @isequiv_inverse' A B f H.

Definition path_contr A {H:Contr A} (x y : A) : x = y
  := concat (eq_sym (@contr _ H x)) (@contr _ H y).

Definition transport_inv A {P : A -> Type} (x y :A) (e : x = y) (u:P x) v:
  u = eq_sym e # v -> e # u = v.
  destruct e. exact id. 
Defined. 

Definition contr_sigma A {P : A -> Type}
  {H : Contr A} `{H0 : forall a, Contr (P a)}
  : Contr (sigma P).
Proof.
  exists (@center _ H; @center _ (H0 (@center _ H))).
  intros [a Ha]. refine (path_sigma _ _ _ _).
  simpl. apply H. simpl. apply transport_inv.
  apply (H0 center).
Defined.

Definition path_sigma_uncurried (A : Type) (P : A -> Type) (u v : sigma P)
  (pq : sigma (fun p => p # u.2 = v.2))
  : u = v.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p. simpl in *. destruct q.
  apply eq_refl.
Defined.

Definition pr1_path A `{P : A -> Type} {u v : sigma P} (p : u = v)
: u.1 = v.1
  := ap (@proj1 _ _) p.

Notation "p ..1" := (pr1_path p) (at level 3).

Definition pr2_path A `{P : A -> Type} {u v : sigma P} (p : u = v)
: p..1 # u.2 = v.2.
  destruct p. apply eq_refl.
Defined.

Notation "p ..2" := (pr2_path p) (at level 3).

Definition eta_path_sigma_uncurried A `{P : A -> Type} {u v : sigma P}
           (p : u = v) : path_sigma_uncurried _ _ (p..1; p..2) = p.
  destruct p. apply eq_refl.
Defined.

Definition eta_path_sigma A `{P : A -> Type} {u v : sigma P} (p : u = v)
: path_sigma _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition path_sigma_equiv {A : Type} (P : A -> Type) (u v : sigma P):
  IsEquiv (path_sigma_uncurried u v).
  refine (BuildIsEquiv _ _ _).
  - exact (fun r => (r..1; r..2)).
  - intro. apply eta_path_sigma.
  - destruct u, v; intros [p q]; simpl in *.
    destruct p. simpl in *. destruct q.
    reflexivity.
  - destruct u, v; intros [p q]; simpl in *;
    destruct p. simpl in *. destruct q; simpl in *.
    apply eq_refl.
Defined.

Instance contr_unit : Contr unit | 0 := let x := {|
  center := tt;
  contr := fun t : unit => match t with tt => eq_refl end
|} in x.


Definition path2_contr A {H:Contr A} {x y : A} (p q : x = y) : p = q.
  assert (K : forall (r : x = y), r = path_contr x y).
  intro r; destruct r; symmetry; now apply concat_Vp.
  apply (transitivity (y:=path_contr x y)).
  - apply K.
  - symmetry; apply K.
Defined.

Instance contr_paths_contr A {H:Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := concat (eq_sym (contr x)) (contr y);
  contr := path2_contr (concat (eq_sym (contr x)) (contr y))
|} in c.

Program Instance contr_prod A B {CA : Contr A} {CB : Contr B} : Contr (prod A B).
Next Obligation. exact (@center _ CA, @center _ CB). Defined.
Next Obligation. apply path_prod; apply contr. Defined.

