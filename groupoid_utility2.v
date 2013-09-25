Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Require Import Setoid.
Set Universe Polymorphism.
Require Import groupoid.
Require Import groupoid_utility.
Require Import groupoid_interpretation_def.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Program Mode.
 
Opaque Equiv_adjoint.
Opaque map_id map_inv Dmap_id.

Definition equiv_adjoint {Γ:Context} {A:Typ Γ} (a:Elt A) 
        {x y : [Γ]} (e : x ~1 y) : a @ x ~1 (adjoint (map A e)) @ (a @ y) :=
  (map (adjoint (map A e)) (Dmap a e)) ° [inverse (retraction (map A e))] (a @ x).

Definition Equiv_adjoint_comp {Γ:Context} {A:Typ Γ} (a:Elt A) (x y z:[Γ]) (e:x~1 y) (e': y ~1 z):
[Equiv_adjoint [map_comp A e e']] ([a] z) ° equiv_adjoint a (e' ° e) ~
   map (adjoint (map A e)) (equiv_adjoint a e') ° equiv_adjoint a e.
unfold equiv_adjoint. simpl.
eapply composition. apply comp. apply comp. apply identity.
eapply composition. apply _map2. apply _Dmap_comp. eapply composition.
apply _map_comp. apply comp. apply identity. apply _map_comp. apply identity.
unfold eq_rect_map, eq_rect_comp.
(* unfold map; simpl. *)
eapply composition. apply comp. apply identity.
apply (Equiv_adjoint_simpl [map_comp A e e']). simpl. simpl_id.
unfold inverse. 
Admitted.

Definition Equiv_adjoint_eq {Γ:Context} {A:Typ Γ} (a:Elt A) (x y:[Γ]) (e e':x~1 y) (E: e ~ e'):
[Equiv_adjoint [map2 A E]] ([a] y) ° equiv_adjoint a e ~
   equiv_adjoint a e'.
  unfold equiv_adjoint. simpl. eapply composition. apply comp.
  apply comp. eapply composition. eapply inv. apply (eq_retraction (map2 A E)). 
  simpl. eapply composition. apply inverse, comp_inv. apply comp. apply identity.
  apply inverse, comp_inv. 
  eapply composition. apply _map2. apply (Dmap2 a E). apply _map_comp. apply identity.
  simpl. 
Admitted.

Definition Equiv_adjoint_identity {Γ:Context} {A:Typ Γ} (a:Elt A) (x:[Γ]) : 
  [Equiv_adjoint [map_id A]] (a @ x) ° equiv_adjoint a (identity x) ~
   identity ([a] x).
  unfold equiv_adjoint. simpl. eapply composition. apply comp.
  apply comp. eapply composition. apply inv. apply (eq_retraction (map_id A)). 
  simpl. simpl_id. apply _map2. apply Dmap_id.  apply identity.
  unfold eq_rect_id. eapply composition. apply comp.
  eapply composition. eapply comp. apply inverse, comp_inv. apply identity. 
  eapply composition. eapply inverse. apply assoc. eapply composition. apply comp. apply identity. 
  eapply inverse.
  exact (α_map (inverse (Equiv_adjoint [map_id A])) ([[map_id A]] ([a] x))). 
  eapply composition. apply assoc. apply comp. apply inv_R. apply identity. apply identity. 
  simpl_id. apply inv_R.
Defined.

Definition ext (Γ: Context) (T : Typ Γ) : Type := 
  @sigma [Γ] (λ γ, [T @ γ]).

Definition cons {Γ: Context} {T : Typ Γ} (γ : [Γ]) (x : [T @ γ]) : ext T := (γ;x).

Definition sum_id_left {Γ: Context} {T : Typ Γ} 
        {γ : [Γ]} {x y : [T @ γ]}  (e : x ~1 y) : (cons γ x) ~1 (cons γ y) :=
   (identity _ ; e ° ([map_id T] @ x)).


Definition sum_id_left_map {Γ: Context} {T : Typ Γ}
        (γ : [Γ])   (x y : [T @ γ])  (e e': x ~1 y) (H : e ~2 e') : 
  sum_id_left e ~2 sum_id_left e'.
exists (identity _). simpl. eapply inverse. eapply composition. 
apply assoc. apply comp; try apply (inverse H). 
eapply composition; try apply id_R. apply comp; try apply identity.
apply (map2_id T _ x). 
Defined.

Definition sum_id_left_comp {Γ: Context} {T : Typ Γ}
        (γ : [Γ]) (x y z: [T @ γ])  (e: x ~1 y) (e' : y ~1 z) : 
  sum_id_left e' ° sum_id_left e ~2 sum_id_left (e' ° e).
exists (id_R _ _ _). simpl. eapply composition.  apply assoc.
eapply composition.  apply assoc. eapply inverse.
eapply composition.  apply assoc. eapply composition.  apply assoc. eapply inverse.
apply comp; try apply identity. eapply composition. apply comp. apply comp.
apply identity. apply (map_comp [map T (identity γ)]).
apply identity. eapply composition. eapply inverse. apply assoc. eapply composition.
apply comp. apply identity. eapply composition. eapply inverse. apply assoc.
apply comp. apply identity. unfold eq_rect,id. 
apply (α_map [map_id T]).
eapply composition. apply assoc. eapply composition. apply assoc. apply comp; try apply identity.
apply comp; try apply identity. 
eapply inverse. eapply composition. apply (map2_id_R _ _ x). simpl. 
eapply composition. apply comp. apply identity. eapply composition. apply id_L.  apply id_R.
apply identity.
Defined.

Definition sum_id_left_id {Γ: Context} {T : Typ Γ}
        (γ : [Γ])  (x : [T @ γ]) :
  sum_id_left (identity x) ~2 identity _.
exists (identity _). simpl. unfold eq_rect_id, eq_rect_eq.
eapply composition. apply id_L. eapply inverse. eapply composition; try apply id_R.
apply comp; try apply identity. apply (map2_id T _ x).
Defined.


(* Definition sum_eq_map (Γ: [_Type]) (T : [Γ --> _Type]) *)
(*         (x y : [Γ]) (X : x ~1 y) (t : [T @ y]) : *)
(*   (x;eq_rect T (inverse X) @ t) ~1 (y;t). *)
(*   exists X. simpl. unfold eq_rect.  *)
(*   eapply composition;  *)
(*     try apply (section (map T X) @ t). *)
(*   exact ([comp _ _ _ _ _ _ _  *)
(*                      (map_inv T _ _ X) (identity _)] @ t). *)
(* Defined. *)

Definition sum_id_right {Γ} {A:Typ Γ} {γ γ' : [Γ]}
  (e : γ ~1 γ') (a' : [A @ γ']) : (cons γ (adjoint (map A e) @ a')) ~1 (cons γ' a').
exists e. apply ((section (map A e)) @ a'). 
Defined.

(* Definition sum_eq_map' (Γ: [_Type]) (T : [Γ --> _Type]) *)
(*         (x y : [Γ]) (X : x ~1 y) (x0 y0 : [T @ y]) (e : x0 ~1 y0): *)
(*   (x;eq_rect T (inverse X) @ x0) ~1 (y;y0). *)
(*   exists X. simpl. unfold eq_rect. *)
(*   eapply composition; *)
(*     try apply (section (map T X) @ y0). *)
(*   eapply composition. *)
(*   exact ([comp _ _ _ _ _ _ _ *)
(*                      (map_inv T _ _ X) (identity _)] @ x0). *)
(*   assert (foo := map [map T X] (map [inverse (map T X)] e)). *)
(*   apply foo. *)
(* Defined. *)

(* Definition map2_id_R_L {Γ: Context} {A : Typ Γ} *)
(*  (x y : [Γ]) (e : x ~1 y) :(id_L x y e) ^-1 ° id_R x y e ~ identity _. *)
(*   map2 A ( (id_L x y e) ^-1 ° id_ x y e) ~ identity _. *)

Definition sum_id_left_right {Γ: Context} {A : Typ Γ}
 (x y : [Γ]) (e : x ~1 y) (t t' : [[A] y]) (e' : t ~1 t'):
  sum_id_left e' ° sum_id_right e t ~
  sum_id_right e t' ° sum_id_left (map (adjoint (map A e)) e').
  exists (inverse  (id_R _ _ _) ° id_L _ _ _). simpl. 
  unfold eq_rect_comp, eq_rect_eq.
  (* apply inverse. eapply composition. apply comp. apply identity. *)
  (* eapply composition. apply comp. apply identity.  *)
  (* eapply composition. apply comp. apply map_comp. apply identity. *)
  (* eapply composition. eapply inverse. apply assoc.  *)
  (* eapply composition. apply comp. apply identity. apply (α_map (section (map A e))). *)
  (* unfold map_id. *)
  (* eapply composition. apply assoc. apply identity. apply identity. *)
  (* eapply composition. apply assoc.   eapply composition. apply assoc.  *)
  (* apply inverse.  eapply composition. apply assoc.   eapply composition. apply assoc.  *)
  (* apply comp; [idtac | apply identity]. *)
 admit.
Defined.

Instance equiveq_pi T U (f g : T <~> U) (α:Equiv_eq f g) : EquivEq [α] := Π2 α.

(* begin hide *)

Instance comp_fun_depfun_1 (T T': [_Type]) (U : [T' --> _Type])
        (F : [T --> T']) (G : [_Prod U]) : WeakDependentFunctor (U ⋅ F) (λ x : [T], G @ (F @ x)).
Next Obligation. apply (Dmap G (map F e)). Defined.
Next Obligation. unfold comp_fun_depfun_1_obligation_1. 
                 eapply composition. apply (Dmap2 G (map_comp F e e')).
                 eapply composition. apply comp. apply identity. 
                 apply (Dmap_comp G). eapply composition. apply assoc. 
                 apply identity.
                 Defined.
Next Obligation. apply (Dmap2 G (map2 F H)). Defined. 

Definition comp_fun_depfun {T T': [_Type]} {U : [T' --> _Type]}
        (F : [T --> T']) (G : [_Prod U]) : [_Prod (U ⋅ F)] :=
(λ x : [T], G @ (F @ x); comp_fun_depfun_1 _ _ _ _ _).

(* end hide *)

Notation  "g '°°' f" := (comp_fun_depfun f g) (at level 50). 



Definition equiv_adjoint_map (Γ: Context) (A : Typ Γ)  (γ γ' : [Γ]) (e0 : γ ~1 γ')
        (x y : Elt A) (e : x ~1 y) : 
   map (adjoint (map A e0)) ([e] γ') ° equiv_adjoint x e0 ~
   equiv_adjoint y e0 ° [e] γ.
Admitted.

(* An other version of prod_eq *)

Program Definition Prod_eq_ {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y) : 
  [F] x ° adjoint (map A e) ~ [F] y 
  := Dmap F e ° inverse (nat_id_L ([F] x ° adjoint (map A e))).

Program Definition Prod_eq_1 {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y)
(X: Prod_Type ([F] x)) (a : [[A] y]) : [[[F] y] a] :=
 [Prod_eq_ F e @ a] @ ((X °° adjoint (map A e)) @ a).

Program Instance Prod_eq_2 {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y)
(X: Prod_Type ([F] x)) : WeakDependentFunctor ([F] y) (Prod_eq_1 F e X) :=
  prod_eq1 (A @ y) _ (F @ y) (Prod_eq_ F e) (X °° adjoint (map A e)).

Program Instance Prod_eq_3 {Γ} (A:Typ Γ) (F:TypFam A) {x y : [Γ]} (e:x~1 y) :
 WeakFunctor   (λ X : [_Prod (F @ x)],
         (λ a, Prod_eq_1 F e X a; Prod_eq_2 A F e X) : [_Prod (F @ y)]).
Obligation Tactic := intros.
Next Obligation. exists (fun a => map [Prod_eq_ F e @ a] 
                                      (X @ ([adjoint (map A e)] a))).
                 econstructor; intros.
                 unfold groupoid_utility.prod_eq1_obligation_1.
                 eapply composition. eapply inverse. apply assoc.
                 eapply composition. apply comp. apply identity.
                 eapply composition. eapply inverse.
                 apply (map_comp [Prod_eq_ F e @ t']).
                 eapply composition. eapply (map2 [Prod_eq_ F e @ t']). 
                 apply (Π2 X).
                 apply (map_comp [Prod_eq_ F e @ t']).
                 unfold eq_rect_map. eapply composition. apply assoc.
                 apply inverse. eapply composition. apply assoc.
                 apply comp; [idtac | apply identity].
                 eapply inverse. eapply composition. eapply inverse.
                 apply (α_map ((inverse [α_map (Prod_eq_ F e) e0]) : nat_trans _ _)).
                 apply comp; [idtac | apply identity].
                 apply identity.
Defined.

Program Instance fun_pi (T U : WeakGroupoidType) (f : T ---> U) : WeakFunctor [f] := Π2 f.
Definition map_comp' {T U} (f:T ---> U) {x y z: [T]} (e: x ~1 y) (e':y ~1 z) :=
  _map_comp (WeakFunctor := proj2 f) x y z e e' : map f (e' ° e) ~ map f e' ° map f e.


Next Obligation. intro. intros. simpl. refine (map_comp' _ _ _). Defined.

Next Obligation. simpl; red; intros; simpl. apply (_map2 _ _ _ _ (X _)). Defined.

Program Definition Prod_eq {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y): 
 _Prod ([F] x) ---> _Prod ([F] y) := (_; Prod_eq_3 A F e).

Program Definition Prod_eq_comp'' {Γ} (A:Typ Γ) (F:TypFam A) {x y z: [Γ]}
        (e:x~1 y) (e' : y ~1 z):
  ∀ t a , [Prod_eq F e' ° Prod_eq F e] t @ a ~1 [Prod_eq F (e' ° e)] t @ a.
intros. simpl. unfold Prod_eq_1. simpl. unfold id.
apply inverse. eapply composition. apply ([Dmap_comp F e e' a]). simpl.
refine (map _ _). refine (map _ _). apply (Dmap t).
Defined.

Program Definition Prod_eq_comp' {Γ} (A:Typ Γ) (F:TypFam A) {x y z: [Γ]}
        (e:x~1 y) (e' : y ~1 z):
  ∀ t , [Prod_eq F e' ° Prod_eq F e] t ~1 [Prod_eq F (e' ° e)] t .
intro. exists (Prod_eq_comp'' F e e' t). intros; simpl. unfold Prod_eq_comp''.
admit. Defined.

Program Definition Prod_eq_comp {Γ} (A:Typ Γ) (F:TypFam A) {x y z: [Γ]}
        (e:x~1 y) (e' : y ~1 z): Prod_eq F e' ° Prod_eq F e ~ Prod_eq F (e' °e).
exists (Prod_eq_comp' F e e'). econstructor. intros. simpl. red. intros. simpl.
simpl_id_bi. unfold Prod_eq_comp'', id. simpl. (* simpl_id_bi. *) admit. Defined.

Program Definition Prod_eq_map' {Γ} (A:Typ Γ) (F:TypFam A) {x y: [Γ]}
        (e e':x ~1 y) (H : e ~ e') t :  
  [Prod_eq F e] t ~1 [Prod_eq F e'] t.
Admitted.

Program Definition Prod_eq_map {Γ} (A:Typ Γ) (F:TypFam A) {x y: [Γ]}
        (e e':x ~1 y) (H : e ~ e') :  Prod_eq F e ~1 Prod_eq F e'.
Admitted.

Program Definition Prod_eq_id {Γ} (A:Typ Γ) (F:TypFam A) {x: [Γ]}
  :  Prod_eq F (identity x) ~1 identity _.
Admitted.

Program Instance Prod_eq_iso {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y) : 
  Iso_struct (Prod_eq F e).
Next Obligation. exact (Prod_eq F (inverse e)). Defined.
Obligation Tactic := idtac.
Next Obligation. intros. unfold Prod_eq_iso_obligation_1.
                 eapply composition. apply Prod_eq_comp. 
                 eapply composition; [idtac | apply Prod_eq_id]. 
                 apply Prod_eq_map. apply inv_R. 
Defined.
Next Obligation. intros. eapply composition. apply Prod_eq_comp. 
                 eapply composition; [idtac | apply Prod_eq_id]. 
                 apply Prod_eq_map. apply inv_L. 
Defined.

Definition Prod_eqT {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y): 
  _Prod (F @ x) <~> _Prod (F @ y) := IsoToEquiv (Prod_eq F e; Prod_eq_iso _ F e).


