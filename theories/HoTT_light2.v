Require Export Unicode.Utf8_core.

Set Universe Polymorphism.

Set Implicit Arguments.

Inductive Empty : Type := .

Definition idmap {A} := fun (x:A) => x.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  eq_rect x P u y p.

Definition transportage {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  eq_rect x P u y p.

Arguments transport {A} P {x y} p u : simpl nomatch.

Lemma transport_const : ∀ (A B : Type) (x y: A) (p:x = y) (y : B),
 transport (fun _ => B) p y = y. intros. destruct p. exact (eq_refl _). 
Defined.

Notation "p # u" := (transport _ p u) (right associativity, at level 65, only parsing).

Definition eq_sym {A : Type} {x y : A} (p : x = y) : y = x
  := match p with eq_refl => eq_refl end.

Arguments eq_sym {A x y} p : simpl nomatch.

(* Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y *)
(*   := match p with eq_refl => eq_refl end. *)

Definition ap := f_equal.

Definition apD {A:Type} {B:A->Type} (f:∀ a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with eq_refl => eq_refl end.

Definition equal_f (A : Type) (P : A -> Type) (f g : forall x, P x) (p : f = g) :
forall x, f x = g x.
intro x. destruct p. reflexivity.
Defined.

Definition ap_map A B (f:A -> B) (a b : A) (p p' : a = b) (q : p = p') : 
  ap f p = ap f p'.
  apply ap. exact q.
Defined.

(** See above for the meaning of [simpl nomatch]. *)
Arguments apD {A B} f {x y} p : simpl nomatch.

Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
Proof.
  destruct p; reflexivity.
Defined.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  eq_rect _ (fun w => w = z) q _ (eq_sym p).

Notation "p @ q" := (concat p q) (at level 20) : type_scope.

Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) :
  apD f p = transport_const p (f x) @ ap f p.
Proof.
  destruct p. reflexivity.
Defined.

Definition ap2 (T U V : Type) (f : T -> U -> V)
           (e e' : T) (h h' : U) (X :e = e') (X':h = h'): f e h = f e' h' :=
  equal_f  _ (ap f X) h @ ap (f e') X'.

Definition ap2_map (T U V : Type) (f : T -> U -> V)
           (e e': T) (h h' : U) (X X' : e = e') (Y Y' : h = h') (H : X = X')
           (H' : Y = Y'): 
  ap2 f X Y = ap2 f X' Y' := ap2 (ap2 f (h':=h')) H H' .


Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_l {A : Type} {y x1 x2 : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = eq_sym p @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition concat_R {A : Type} {x y z : A} (p p': x = y) (q : y = z) (e: p = p'): p @ q = p' @ q
  := ap (fun p => p @ q) e.

Definition concat_L {A : Type} {x y z : A} (p : x = y) (q q' : y = z) (e: q = q'): p @ q = p @ q'
  := ap (concat p) e.

Definition concat_LR {A : Type} {x y z : A} (p p': x = y) (q q' : y = z) 
  (e : p = p') (e': q = q') : p @ q = p' @ q' := ap2 concat e e'. 

Definition concat_R_map {A : Type} {x y z : A} (p p': x = y) (q : y = z) (e e': p = p') (H : e = e')
  : concat_R q e = concat_R q e' := ap_map (fun p => p @ q) H.

Definition concat_L_map {A : Type} {x y z : A} (p : x = y) (q q': y = z) (e e': q = q') (H : e = e')
  : concat_L p e = concat_L p e' := ap_map (concat p) H.

Definition concat_LR_map {A : Type} {x y z : A} (p p': x = y) (q q': y = z) (e e': p = p') (f f' : q = q')
           (H : e = e') (H' : f = f')
  : concat_LR e f = concat_LR e' f' := ap2_map concat H H'. 

Definition concat_assoc {A : Type} {x y z w : A} (p : x = y) (q : y = z) (r : z = w) : 
  (p @ q) @ r = p @ (q @ r).
destruct p. reflexivity. Defined.

Lemma ap_concat A B (f:A -> B) (a b c : A) (p : a = b) (q : b = c) : 
  ap f (p @ q) = ap f p @ ap f q.
  destruct p. reflexivity.
Defined.

Lemma ap2_concat A B C (f:A -> B -> C) (a b c : A) (p : a = b) (q : b = c) 
      (a' b' c' : B) (p' : a' = b') (q' : b' = c') : 
  ap2 f (p @ q) (p' @ q') = ap2 f p p' @ ap2 f q q'.
  destruct p, p'. reflexivity.
Defined.

Definition ap2_map_concat (T U V : Type) (f : T -> U -> V)
           (e e': T) (h h' : U) (X X' X'': e = e') (Y Y' Y'': h = h') 
           (H : X = X') (H' : X' = X'')
           (G : Y = Y') (G':Y' = Y''):
  ap2_map f H G @ ap2_map f H' G' = ap2_map f (H@H') (G@G') :=
  eq_sym (ap2_concat (ap2 f (h':=h')) H H' G G').

Definition concat_R_concat {A : Type} {x y z : A} (p p' p'': x = y) (q : y = z) 
           (e : p = p') (e' : p' = p'') 
  : concat_R q (e @ e') = concat_R q e @ concat_R q e' := ap_concat (fun p => p @ q) e e'.

Definition concat_L_concat {A : Type} {x y z : A} (p : x = y) (q q' q'' : y = z) 
           (e : q = q') (e' : q' = q'') 
  : concat_L p (e @ e') = concat_L p e @ concat_L p e' := ap_concat (concat p) e e'.

Definition concat_LR_concat {A : Type} {x y z : A} (p p' p'': x = y) (q q' q'': y = z) 
           (e : p = p') (e' : p' = p'') (f : q = q') (f' : q' = q'')
  : concat_LR (e @ e') (f @ f') = concat_LR e f @ concat_LR e' f' := 
  ap2_concat concat e e' f f'.

Lemma ap_id A (a b : A) (p : a = b) :
  ap (fun x =>  x) p = p.
destruct p.
reflexivity.
Defined.

Lemma ap_inv A B (f:A -> B) (a b : A) (p : a = b) :
  eq_sym (ap f p) = ap f (eq_sym p).
  destruct p. reflexivity.
Defined.

Lemma eq_sym_inv_L A (x y : A) (p : x = y) : eq_sym p @ p = eq_refl _.
  destruct p. reflexivity.
Defined.

Lemma eq_sym_inv_R A (x y : A) (p : x = y) : p @ eq_sym p = eq_refl _.
  destruct p. reflexivity.
Defined.

Lemma idpath_L {A : Type} {x y: A} (p : x = y) : (eq_refl _) @ p = p.
destruct p. reflexivity. Defined.

Lemma idpath_R {A : Type} {x y: A} (p : x = y) : p @ (eq_refl _) = p.
destruct p. reflexivity. Defined.

Lemma cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : (p @ q = p @ r) -> (q = r).
Proof.
  destruct p, r.
  intro a. exact (eq_sym (idpath_L q) @ a).
Defined.

Lemma cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : (p @ r = q @ r) -> (p = q).
Proof.
  destruct r, p.
  intro a.
  exact (a @ idpath_R q).
Defined.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with eq_refl =>
    match p with eq_refl => eq_refl end
  end.

Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2)
  : (transport (fun x => B x -> C x) p f) y  =  p # (f (eq_sym p # y)).
Proof.
  destruct p; simpl; auto.
Defined.

Definition ap_sym {A B:Type} (f:A -> B) {x y:A} (p:x = y) : ap f (eq_sym p) = eq_sym (ap f p) :=
  match p with eq_refl => eq_refl end.


Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with eq_refl => z end.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # eq_sym p # z = z
  := eq_sym (transport_pp P (eq_sym p) p z)
  @ ap (fun r => transport P r z) (eq_sym_inv_L p).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type
  := forall x:A, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition transport_forall
  {A : Type} {P : A -> Type} {C : forall x, P x -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y)
  : (transport (fun x => forall y : P x, C x y) p f)
    == (fun y =>
       transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (eq_sym p # y))))
  := match p with eq_refl => fun _ => eq_refl _ end.


Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  : transport (fun x => x = x) p q = eq_sym p @ q @ p.
Proof.
  destruct p; simpl.
  rewrite <- ((eq_sym (idpath_L q))). 
  apply (eq_sym (idpath_R q)). 
Defined.

Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = eq_sym p # v -> p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> eq_sym p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.


Definition equal_f_eq (A : Type) (P : A -> Type) (f g : forall x, P x) (p : f = g) x y (q : y = x) : equal_f P p x = transport (fun x => f x = g x) q (equal_f P p y).
  destruct p, q. reflexivity.
Defined.

Definition transport2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : P x)
  : p # z = q # z
  := ap (fun p' => p' # z) r.



Definition eq_transport {A : Type} (B : A -> Type) (g : forall a:A, B a -> B a)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (q : y = g x1 y) : p # y = transport (λ a : A, B a → B a) p (g x1) (p # y).
  destruct p. exact q. Defined.

Definition transportD_eq {A : Type} (B : A -> Type) (g : forall a:A, B a -> B a)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (q : y = g x1 y)
  : transportD B (fun a b => b = g a b) p y q =
    (eq_transport _ _ p q) @ equal_f _ (apD g p) (p # y).
  destruct p. apply (eq_sym (idpath_R _)).
Defined.


Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (fun x => f x = y) p q = eq_sym (ap f p) @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  : transport (fun x => g (f x) = x) p q = eq_sym (ap g (ap f p)) @ q @ p.
Proof.
  destruct p; simpl.
  exact (eq_sym (idpath_L q) @ eq_sym (idpath_R ((eq_refl _) @ q))).
Defined.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).


Definition projT1_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : u.1 = v.1 := ap (@projT1 _ _) p.

Notation "p ..1" := (projT1_path p) (at level 3).

Definition projT1_path_1 {A : Type} {P : A -> Type} (u : sigT P)
: (eq_refl u) ..1 = eq_refl (u .1)
:= eq_refl _.


Definition projT2_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : p..1 # u.2 = v.2
  := eq_sym (transport_compose P (@projT1 _ _) p u.2)
     @ (@apD {x:A & P x} _ (@projT2 _ _) _ _ p).

Notation "p ..2" := (projT2_path p) (at level 3).

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (pq : {p : u.1 = v.1 &  p # u.2 = v.2})
  : u = v.
  destruct pq, u ,v. simpl in *. 
  destruct x. simpl in *. destruct e. reflexivity. 
Defined.


Definition pr1_path_sigma_uncurried A `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition pr2_path_sigma_uncurried A `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ pq)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma_uncurried pq) @ pq.2.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma_uncurried A `{P : A -> Type} {u v : sigT P}
           (p : u = v)
: path_sigma_uncurried _ _ (p..1; p..2) = p.
Proof.
  destruct p. destruct u. reflexivity.
Defined.

Definition path_sigma_id A `{P : A -> Type} (u : sigT P) :
           eq_refl u = path_sigma_uncurried u u (eq_refl _ ; eq_refl _ ).
  destruct u. reflexivity.
Defined.

Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : p # y = y')
: (x;y) = (x';y').
  apply path_sigma_uncurried. exists p. exact q.
Defined.

  (* := match pq with *)
  (*      | existT _ p q => *)
  (*        match u, v return (forall p0, (p0 # u.2 = v.2) -> (u=v)) with *)
  (*          | (x;y), (x';y') => fun p1 q1 => *)
  (*            match p1 in (_ = x'') return (forall y'', (p1 # y = y'') -> (x;y)=(x'';y'')) with *)
  (*              | eq_refl => fun y' q2 => *)
  (*                match q2 with *)
  (*                  | eq_refl => eq_refl (x,y) *)
  (*                end *)
  (*            end y' q1 *)
  (*        end p q *)
  (*    end. *)

Definition projT1_path_sigma_uncurried {A} {P : A -> Type} {u v : sigT P}
  (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
  : (path_sigma_uncurried _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

(* Axiom UIP_refl : forall (U:Set) (x:U) (p:x = x), p = eq_refl x. *)

(* Lemma existT_destruct2 (A:Set) (P : A -> Type)  (a:A) (t t' : P a) : (a;t) = (a;t') ->  t = t'. *)
(*   intro e. pose (H := e..2). simpl in H. rewrite <- H.  *)
(*   rewrite (UIP_refl (e..1)). reflexivity. *)
(* Defined. *)

Definition eq_sym_sym A (a b:A) (e:a=b) : eq_sym (eq_sym e) = e.
destruct e; reflexivity. Defined.

Definition eq_sym_1 A {P : A -> Type} {u v : sigT P} (p : u = v) : (eq_sym p)..1 = eq_sym (p..1).
destruct p; reflexivity. Defined.


Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y })
  : transport (fun x => { y : B x & C x y }) p yz
    = (p # yz.1 ; transportD _ _ p yz.1 yz.2).
Proof.
  destruct p.  destruct yz as [y z]. reflexivity.
Defined.

Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
  : transport (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.


Definition sum_forall_adjoint A P B (f : ∀ x : A, P x -> B) : {x : A & P x} -> B. 
  intros. destruct X. exact (f x p). Defined.

Definition forall_sum_adjoint A P B (f : {x : A & P x} -> B) : ∀ x : A, P x -> B. 
  intros. exact (f (x; X)). Defined.

Definition sum_forall_adjoint_eq' A P B (f g : ∀ x : A, P x -> B) : (forall x , f x = g x) ->
  forall x, sum_forall_adjoint _ f x = sum_forall_adjoint _ g x.
  intros e x. destruct x. exact (equal_f _ (e x) p).
Defined.


Definition transport_funR {A B B': Type} {f : A -> B} (x:A) (p:B = B'):
  transport (id (A:=Type)) p (f x) = transport (λ B, A -> B) p f x.
  destruct p. reflexivity.
Defined.

Definition transport_funL {A B A': Type} {f : A -> B} (x:A') (p:A = A'):
  f (transport (id (A:=Type)) (eq_sym p) x) = transport (λ A, A -> B) p f x.
  destruct p. reflexivity.
Defined.

Definition transport_comp A B (b b': A) (c c' : B) P (f : P b c) e e':
  transport (fun b => P b c') e (transport (fun c => P b c) e' f) =
  transport (fun c => P b' c) e' (transport (fun b => P b c) e f). 
  destruct e, e'. reflexivity. Defined.



Definition transport_Hom {Obj Obj' T: Type} {Hom : Obj -> Obj -> T}
  {Hom' : Obj' -> Obj' -> T} {x1 x2 : Obj} (p : existT (λ Obj, Obj → Obj → T) Obj Hom = (Obj';Hom')) :
Hom x1 x2 =
   transport (λ Obj0 : Type, Obj0 → Obj0 → T) p ..1 Hom
     (transport (id (A:=Type)) p ..1 x1) (transport (id (A:=Type)) p ..1 x2).
  destruct p. reflexivity.
Defined.

Definition transport_Hom2 {Obj Obj' T: Type} {Hom : Obj -> Obj -> T}
  {Hom' : Obj' -> Obj' -> T} {x1 x2 : Obj'} (p : existT (λ Obj, Obj → Obj → T) Obj Hom = (Obj';Hom')) :
Hom (transport (id (A:=Type)) (eq_sym p ..1) x1) (transport (id (A:=Type)) (eq_sym p ..1) x2) =
   transport (λ Obj0 : Type, Obj0 → Obj0 → T) p ..1 Hom
     x1 x2.
  pose (H:=transport_Hom p (x1:=transport (id (A:=Type)) (eq_sym p ..1) x1) (x2:=transport (id (A:=Type)) (eq_sym p ..1) x2)). 
  etransitivity; try exact H. repeat rewrite <- transport_pp. 
  repeat rewrite eq_sym_inv_L. reflexivity.
Defined.

Definition transport_Hom' {Obj Obj' T: Type} {Hom : Obj -> Obj -> T}
  {Hom' : Obj' -> Obj' -> T} {x1 x2 : Obj} (p : existT (λ Obj, Obj → Obj → T) Obj Hom = (Obj';Hom'))
: Hom x1 x2 = Hom' (transport (id (A:=Type)) (p..1) x1) (transport (id (A:=Type)) (p..1) x2). 
Proof.
  pose (foo := equal_f _ (equal_f _ p..2 (transport (id (A:=Type)) p ..1 x1)) (transport (id (A:=Type)) p ..1 x2)). simpl in foo. etransitivity; try exact foo. clear foo.
  apply transport_Hom. Defined.


(** With this version of the function, we often have to give [z] and [z'] explicitly, so we make them explicit arguments. *)
Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z').
Proof.
  destruct z, z'. simpl in *.
  case (fst pq). case (snd pq).
  reflexivity.
Defined.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).


Definition section {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : section equiv_inv f;
  eissect : section f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.
Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.


Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'").
Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

(** We will use [Notation] for [trunc_index]es, so define a scope for them here. *)
Delimit Scope trunc_scope with trunc.
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%trunc_scope.

Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0 => trunc_S (trunc_S minus_two)
       | S n' => trunc_S (nat_to_trunc_index n')
     end.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Notation minus_one:=(trunc_S minus_two).
(** Include the basic numerals, so we don't need to go through the coercion from [nat], and so that we get the right binding with [trunc_scope]. *)
Notation "0" := (trunc_S minus_one) : trunc_scope.
Notation "1" := (trunc_S 0) : trunc_scope.
Notation "2" := (trunc_S 1) : trunc_scope.

Arguments IsTrunc_internal n A : simpl nomatch.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

(** We use the priciple that we should always be doing typeclass resolution on truncation of non-equality types.  We try to change the hypotheses and goals so that they never mention something like [IsTrunc n (_ = _)] and instead say [IsTrunc (S n) _].  If you're evil enough that some of your paths [a = b] are n-truncated, but others are not, then you'll have to either reason manually or add some (local) hints with higher priority than the hint below, or generalize your equality type so that it's not a path anymore. *)

Typeclasses Opaque IsTrunc. (* don't auto-unfold [IsTrunc] in typeclass search *)

Arguments IsTrunc : simpl never. (* don't auto-unfold [IsTrunc] with [simpl] *)

Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A)
: IsTrunc n (x = y)
  := H x y. (* but do fold [IsTrunc] *)

Notation Contr := (IsTrunc minus_two).

Notation IsHProp := (IsTrunc minus_one).

Notation IsHSet := (IsTrunc 0).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

Lemma contr_inhabited_hprop (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
Proof.
  exists x.
  intro y.
  destruct (H x y). exact center0.
Defined.

Definition path_contr (A:Type) `{Contr A} (x y : A) : x = y
  := eq_sym (contr x) @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. *)
Definition path2_contr (A:Type) `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    intro r; destruct r; symmetry; now apply eq_sym_inv_L.
  transitivity (path_contr x y);auto.
Defined.

Instance contr_paths_contr (A:Type) `{Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := eq_sym (contr x) @ contr y;
  contr := path2_contr (eq_sym (contr x) @ contr y)
|} in c.

(** If inhabitation implies contractibility, then we have an h-proposition.  We probably won't often have a hypothesis of the form [A -> Contr A], so we make sure we give priority to other instances. *)
Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A | 10000.
Proof.
  intros H x y.
  pose (C := H x).
  apply contr_paths_contr. exact C.
Defined.



Theorem allpath_hprop (A : Type) `{H : IsHProp A} : forall x y : A, x = y.
Proof.
  apply H.
Defined.

Theorem hprop_allpath (A : Type) : (forall (x y : A), x = y) -> IsHProp A.
  intros H x y.
  pose (C := @BuildContr A x (H x)).
  apply contr_paths_contr.
  exact C.
Defined.

Definition axiomK A := forall (x : A) (p : x = x), p = eq_refl x.

Definition axiomK_hset {A} : IsHSet A -> axiomK A.
Proof.
  intros H x p.
  apply (H x x p (eq_refl x)).
Defined.

Definition hset_axiomK {A} `{axiomK A} : IsHSet A.
Proof.
  intros x y H.
  apply @hprop_allpath.
  intros p q. destruct q. apply axiomK0.
Defined.

Definition HSet := {S : Type & IsHSet S}.

Instance HSet_IsHSet (S : HSet) : IsHSet S.1 := S.2.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'").
Notation "A <~> B" := (Equiv A B) (at level 85).
Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.


Definition moveL_equiv_M A B f  `{IsEquiv A B f} (x : A) (y : B) (p : f ^-1 y = x)
  : (y = f x)
  := eq_sym (eisretr f y) @ ap f p.

Definition moveR_equiv_M A B f `{IsEquiv A B f} (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y)
  := ap f p @ eisretr f y.

Lemma contr_equiv A B `(f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (@center A _)).
  intro y.
  eapply moveR_equiv_M.
  apply contr.
Qed.

Definition contr_equiv' A B `(f : A <~> B) `{Contr A}
  : Contr B
  := @contr_equiv _ _ (equiv_fun f) (equiv_isequiv f) _.

Definition trunc_equiv A B n `(f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B f ?.
  - exact (@contr_equiv  _ _ f H0 _).
  - intros x y.
    admit.
    (* exact (I (f^-1 x = f^-1 y) (H (f^-1 x) (f^-1 y)) (x = y) ((@ap _ _ (f^-1) _ _)^-1) _). *)
Qed.

Definition trunc_equiv' A B n `(f : A <~> B) {H : IsTrunc n A}
  : IsTrunc n B
  := @trunc_equiv _ _ n (equiv_fun f) H (equiv_isequiv f).

Definition equiv_path_prod {A B : Type} (z z' : A * B)
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z').
Admitted.
  (* := BuildEquiv _ _ (path_prod_uncurried z z') _. *)

Instance trunc_prod A B n `{IsTrunc n A} `{IsTrunc n B} : IsTrunc n (A * B) | 100.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [| n I]; simpl; (intros A ? B ?).
  { exists (@center A _, @center B _).
    intros z; apply path_prod; apply contr. }
  { intros x y.
    exact (trunc_equiv' n (equiv_path_prod x y)). }
Defined.


Instance trunc_forall A n `{P : A -> Type} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (forall a, P a).
Admitted.

Global Instance trunc_sigma A n `{P : A -> Type}
         `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
: IsTrunc n (sigT P) | 100.
Admitted.
(* Proof. *)
(*   generalize dependent A. *)
(*   induction n; simpl; intros A P ac Pc. *)
(*   { exists (center; center (P (center A))). *)
(*     intros [a ?]. *)
(*     refine (path_sigma' P (contr a) (path_contr _ _)).  *)
(* } *)
(*   { intros u v. *)
(*     apply (@trunc_equiv _ _ n (path_sigma_uncurried u v)). *)
(*     admit. admit. *)
(*  } *)
(* Defined. *)

Module Export Trunc.

Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
  tr : A -> Trunc n A.
Bind Scope trunc_scope with Trunc.
Arguments tr {n A} a.

(** Make the priority 1, so that we don't override, e.g., [Unit]. *)
Instance istrunc_truncation : forall n A, IsTrunc n (Trunc n A) | 1.
Admitted.

Definition Trunc_rect {n A}
  (P : Trunc n A -> Type) `{forall aa, IsTrunc n (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
:= (fun f aa => match aa with tr a => f a end).

Definition Trunc_rect4 {n A B C D}
  (P : Trunc n A -> Trunc n B -> Trunc n C -> Trunc n D -> Type) 
  `{forall aa bb cc dd, IsTrunc n (P aa bb cc dd)}
  : (forall a b c d, P (tr a) (tr b) (tr c) (tr d)) -> 
    (forall aa bb cc dd, P aa bb cc dd).
  intros. apply Trunc_rect; try apply H.
  apply (@Trunc_rect n C (fun cc => ∀ d : D, P aa bb cc (tr d))).
  intros; apply trunc_forall. intros; apply H.
  apply (@Trunc_rect n B (fun bb => ∀ (c:C) (d : D), P aa bb (tr c) (tr d))).
  repeat (intros; apply trunc_forall). intros; apply H.
  apply (@Trunc_rect n A (fun aa => ∀ (b:B) (c:C) (d : D), P aa (tr b) (tr c) (tr d))).
  repeat (intros; apply trunc_forall). intros; apply H.
  apply X. 
Defined.

End Trunc.

(** The non-dependent version of the eliminator. *)

Definition Trunc_rect_nondep {n A X} `{IsTrunc n X}
  : (A -> X) -> (Trunc n A -> X)
:= Trunc_rect (fun _ => X).

Definition hSet (T : Type) : HSet := (Trunc 0 T; istrunc_truncation 0 T).


Definition HProp := {P : Type & IsHProp P}.

Definition squash := Trunc minus_one.

Definition hProp (T : Type) : HProp := (squash T; istrunc_truncation minus_one T).



Instance trunc_succ A n `{IsTrunc n A} : IsTrunc (trunc_S n) A.
Admitted.


Definition IsHProp_IsHSet (S : HSet) (x y : S.1) : IsHProp (x = y).
apply hprop_inhabited_contr. intro H. exists H. intro H'. apply (S.2).
Defined.  



Definition decidable_paths (A : Type) :=
  forall (x y : A), (x = y) + (~ (x = y)).

(* Usually this lemma would be proved with [discriminate], but unfortunately that tactic is hardcoded to work only with Coq's [Prop]-valued equality.
   TODO: This should be in types/Sum. *)
Definition inl_injective {A B : Type} {x y : A} (p : inl B x = inl B y) : x = y :=
  (@transport _ (fun (s : A + B) => x = (match s with inl a => a | inr b => x end)) _ _ p (eq_refl x)).

Theorem axiomK_decidable {A : Type} : @decidable_paths A -> @axiomK A.
Proof.
Admitted.

Corollary hset_decidable {A : Type} : @decidable_paths A -> IsHSet A.
Proof.
  intro.
  apply @hset_axiomK. apply @axiomK_decidable. exact X.
Defined.


Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with eq_refl _ => eq_refl _ end.

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Axiom funext : Funext.

Instance isequiv_inverse A B (f:A -> B) (H:IsEquiv f) : IsEquiv (f^-1) | 1000
    := BuildIsEquiv (@eissect _ _ f _) (@eisretr _ _ f _) _.
admit. Defined. 

