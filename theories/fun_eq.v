Require Export Unicode.Utf8_core.
Require Coq.Program.Tactics.
Require Import HoTT_light groupoid.

Set Universe Polymorphism.
Set Implicit Arguments.
Set Program Mode.

Set Primitive Projections.

Opaque map_inv.
Notation α_map f := ((proj2 f) _ _).

(******* Groupoud_utility **********)

Infix "--->" := Fun_Type (at level 55). 

Program Instance left_comp_1 A B C (f: [A --> B]) : Functor (λ g : [B --> C], g ° f : [A-->C]).
Next Obligation. exists (fun t => X @ (f @ t)). red. 
                 intros. apply (α_map X). Defined.
Next Obligation. unfold left_comp_1_obligation_1. simpl.
                 exact (fun t => identity _). Defined.
Next Obligation. unfold left_comp_1_obligation_1. simpl.
                 exact (fun t => identity _). Defined.
Next Obligation. unfold left_comp_1_obligation_1. simpl.
                 exact (fun t => X (f @ t)). Defined.

Program Definition left_comp A B C (f: [A --> B]) : (B --> C) ---> (A --> C) :=
  (fun g => g ° f; left_comp_1 _ _ _ _).

Program Instance right_comp_1 A B C (g: [B --> C]) : Functor (λ f : [A --> B], g ° f : [A-->C]).
Next Obligation. exists (fun t => map g (X @ t)). red.
                 intros. simpl. unfold groupoid.arrow_comp_obligation_1. 
                 eapply composition. eapply inverse. apply (map_comp g).
                 eapply inverse. eapply composition. eapply inverse. apply (map_comp g).
                 eapply inverse. apply (map2 g (α_map X e)). Defined.
Next Obligation. exact (fun t => map_id g). Defined.
Next Obligation. exact (fun t => map_comp g (e @ t) (e' @ t)). Defined.
Next Obligation. exact (fun t => map2 g (X t)). Defined.

Program Definition right_comp A B C (g: [B --> C]) : (A --> B) ---> (A --> C) :=
  (fun f => g ° f; right_comp_1 _ _ _ _).

Definition fun_eq {T T' U U': UGroupoidType} (e:T <~> T') (e': U <~> U') : 
  (T --> U) ---> (T' --> U') := right_comp T' [e'] ° left_comp U (adjoint e).

Definition right_comp_eq (T T' U : UGroupoidType) (f f':[T --> T'])
           (H : f ~2 f')  : right_comp U f ~2 right_comp U f'.
exists (fun g => nat_comp' (identity g) H). red.
intros; simpl. red. simpl. intro. simpl_id_bi. eapply inverse. apply (α_map H). 
Defined.

Definition right_comp_eq' (T T' T'' U : UGroupoidType) (f:[T --> T']) (f' :[T' --> T''])
           : right_comp U (f' ° f) ~2 right_comp U f' ° right_comp U f.
exists (fun g => nat_assoc g f f'). red.
intros; simpl. red. intro. simpl. simpl_id_bi. Defined.

Definition left_comp_eq (T U U' : UGroupoidType) (g g':[U --> U'])
           (H : g ~2 g')  : left_comp T g ~2 left_comp T g'.
exists (fun f => nat_comp' H (identity f)). red.
intros; simpl. red. simpl. intro. simpl_id_bi. apply (α_map e).
Defined.

Definition nat_assoc_inv (T U U' U'' : UGroupoidType) (g:[U --> U']) (g' :[U' --> U'']) (f : U'' ---> T) :
  (f ° (g' ° g)) ~1 ((f ° g') ° g).
  red; apply inverse. refine (nat_assoc g g' f). Defined.

Definition left_comp_eq' (T U U' U'' : UGroupoidType) (g:[U --> U']) (g' :[U' --> U'']) 
           : left_comp T (g' ° g) ~2 left_comp T g ° left_comp T g'.
  exists (nat_assoc_inv g g'). red. intros.
  simpl. intro. simpl. simpl_id_bi'. apply identity. Defined.

Definition right_left_comp (T T' U U' : UGroupoidType) (g :[T --> T']) (f: [U --> U'])
           : right_comp T f ° left_comp U g ~1 left_comp U' g ° right_comp T' f.
simpl. red. simpl. exists (fun t => nat_assoc_inv g t f). red. intros.
  simpl. intro. simpl. simpl_id_bi'. apply identity. Defined.

Definition left_comp_id (T U : UGroupoidType) : left_comp T (identity U) ~2 identity _.
  exists (fun t => nat_id_R t). red. intros. simpl. 
  intro. simpl. simpl_id_bi. Defined.

Definition right_comp_id (T U : UGroupoidType) : right_comp U (identity T) ~2 identity _.
  exists (fun t => nat_id_L t). red. intros. simpl. 
  intro. simpl. simpl_id_bi. Defined.

Typeclasses Transparent nat_trans. 

Program Instance fun_eq2 (T T' U U' : UGroupoidType) (e:T <~> T') (e': U <~> U') : Iso_struct (fun_eq e e').
Next Obligation. exact (right_comp T (adjoint e') ° left_comp U' [e]). Defined.
Next Obligation. 
  unfold fun_eq, fun_eq2_obligation_1. eapply composition. 
  apply nat_assoc. eapply composition.  apply nat_comp'. apply nat_comp'.
  apply right_left_comp. apply identity. apply identity. 
  eapply composition. apply nat_comp'. eapply composition. eapply inverse. apply nat_assoc.
  eapply composition. 
  apply nat_comp'. apply identity. eapply composition. eapply inverse. apply left_comp_eq'.
  eapply composition. apply left_comp_eq. apply (section e). apply left_comp_id.
  apply nat_id_L. apply identity. eapply composition. eapply inverse. apply right_comp_eq'.
  eapply composition. apply right_comp_eq. apply (section e'). apply right_comp_id.
Defined.

Next Obligation. 
  unfold fun_eq, fun_eq2_obligation_1. eapply composition.
  apply nat_assoc. eapply composition.  apply nat_comp'. apply nat_comp'.
  apply right_left_comp. apply identity. apply identity. 
  eapply composition. apply nat_comp'. eapply composition. eapply inverse. apply nat_assoc.
  eapply composition. 
  apply nat_comp'. apply identity. eapply composition. eapply inverse. apply left_comp_eq'.
  eapply composition. apply left_comp_eq. eapply inverse. apply (inverse (retraction e)). apply left_comp_id.
  apply nat_id_L. apply identity. eapply composition. eapply inverse. apply right_comp_eq'.
  eapply composition. apply right_comp_eq. eapply inverse. apply (inverse (retraction e')). apply right_comp_id.
Defined.

Definition fun_eqT (T T' U U' : UGroupoidType) (e:T <~> T') (e': U <~> U') : (T --> U) <~> (T' --> U')
  := IsoToEquiv (fun_eq e e'; fun_eq2 _ _ _ _ _ _).

Definition fun_eq_eq (T T' U U' : UGroupoidType) (e e':T <~> T') (f f': U <~> U')
           (H : Equiv_eq e e') (H' : Equiv_eq f f') : fun_eq e f ~1 fun_eq e' f' :=
nat_comp' (left_comp_eq _ (Equiv_adjoint [H])) (right_comp_eq _ [H']).

Definition fun_eq_eq' (T T' T'' U U' U'' : UGroupoidType) (e:T <~> T') (e':T' <~> T'') 
           (f : U <~> U') (f' : U' <~> U'') : 
  fun_eq (e' ° e) (f' ° f) ~1 fun_eq e' f' ° fun_eq e f.
eapply composition. apply nat_comp'. apply left_comp_eq'. apply right_comp_eq'.
eapply composition. apply nat_assoc. eapply inverse.
eapply composition. apply nat_assoc. apply nat_comp'; try apply identity.
eapply composition. eapply inverse. apply nat_assoc. eapply inverse.
eapply composition. eapply inverse. apply nat_assoc. apply nat_comp'; try apply identity.
apply right_left_comp. Defined.

Program Definition fun_eq_map {Γ : UGroupoidType} (A: [Γ --> _Type]) (x y z : [Γ]) (e : x ~1 y) (e' : y ~1 z) : 
  fun_eq (map A (e' ° e)) (identity _Type) ~1
  fun_eq (map A e') (identity _Type) ° fun_eq (map A e) (identity _Type).
eapply composition. apply fun_eq_eq. apply (map_comp A). eapply inverse.
apply (@id_R _ Equiv_cat). 
apply fun_eq_eq'. Defined.

Program Definition fun_eq_id {Γ : UGroupoidType} (A: [Γ --> _Type]) (x : [Γ]) :
  fun_eq (map A (identity x)) (identity _Type) ~1
  identity _.
eapply composition. apply fun_eq_eq. apply (map_id A). apply identity. 
unfold fun_eq. eapply composition. apply nat_comp'. apply left_comp_id. 
apply right_comp_id. apply nat_id_L. Defined.


Definition fun_eq_map' {Γ : [Type0]} (A: [ [[Γ]] --> Type0 ])
        (x y z : [Γ]) (e : x ~1 y) (e' : y ~1 z) :
  (fun_eq (map A (e' ° e)) (identity (Identity := _Type_id) Type0))
  ~1 ((fun_eq (map A e') (identity (Identity := _Type_id) Type0)) ° (fun_eq (map A e) (identity (Identity := _Type_id) Type0))).
eapply composition. apply fun_eq_eq. apply (map_comp A). eapply inverse.
apply (id_R (CategoryP:=Equiv_cat)).
apply fun_eq_eq'. Defined.

Definition equiv_eq_nat_trans :forall {A B : SetoidType} (f g : A <~> B), [f] ~ [g] -> f ~ g.
  intros. exists X. apply AllEquivEq_Setoid. 
Defined.

Program Definition fun_eq_id' {Γ : [Type0]} (A: [ [[Γ]] --> Type0 ]) (x : [Γ]) :
  fun_eq (map A (identity x)) (identity (Identity := _Type_id) Type0) ~1
  identity ( [[[ A ]]] @ x -||-> Type0).
eapply composition. apply fun_eq_eq. apply (map_id A). apply identity. 
unfold fun_eq. eapply composition. apply nat_comp'. apply left_comp_id. 
apply right_comp_id. apply nat_id_L. Defined.

Opaque Equiv_adjoint. 

Definition Equiv_ajoint_map_id {Γ : [Type0]} (A: [ [[Γ]] --> Type0 ]) (x : [Γ]) t t0
(H:=fun_eq_id' A x: [fun_eqT (map A (identity x)) (identity Type0)] ~1
                    [@identity _ _ _Type_id (([[[A]]]) @ x -||-> Type0)]) :
  Equiv_adjoint H @ t @ t0 ~ map t ([map_id A] @ t0). 
  apply equiv_eq_nat_trans. red. red.  simpl. 
  match goal with | [ |- sigma (λ α : ?H, _)]
                    => assert H end. 
  intro. Transparent Equiv_adjoint. simpl. unfold id. Opaque Equiv_adjoint. 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  apply (map2 t). trunc1_eq_expl (A @ x).
  exists X. red; intros. trunc1_eq_expl (t@t0).
Defined. 

Unset Printing Primitive Projection Parameters.

Definition fun_eq_idT {Γ : [Type0]} (A: [ [[Γ]] --> Type0 ]) (x : [Γ]) :
  Equiv_eq (fun_eqT (map A (identity x)) (identity Type0)) 
           (@identity _ _ _Type_id (([[[A]]]) @ x -||-> Type0)) := (fun_eq_id' A x; _ ).
Next Obligation.
    intro. intro. apply equiv_eq_nat_trans. 
    Opaque composition. simpl. red.
    Set Program Mode. unfold id. 
    econstructor. Unshelve. Focus 2.
    intro. Transparent composition. simpl.
    unfold id. 
    eapply composition. eapply inverse. apply (map_comp t). 
    eapply composition. eapply (map [map t _]). 
    eapply inverse. apply (map_inv t). 
    eapply composition. eapply inverse. apply (map_comp t). 
    apply inverse. eapply composition. apply Equiv_ajoint_map_id.
    eapply composition. eapply inverse. apply (map_comp t).
    apply (map2 t). trunc1_eq_expl (A @ x).
    red; intros. trunc1_eq_expl (t @ t0).
Defined.

Definition Equiv_adjoint_map_comp {Γ : [Type0]} (A: [ [[Γ]] --> Type0 ])  (x y z :[Γ])
           (e : x ~1 y) (e' : y ~1 z) t t0
           (H := fun_eq_map' A x y z e e' : [fun_eqT (map A (e' ° e)) (@identity _ _ _Type_id Type0)] ~1 [fun_eqT (map A e') (@identity _ _ _Type_id Type0) ° fun_eqT (map A e) (@identity _ _ _Type_id Type0)]) : (Equiv_adjoint H @ t) @ (adjoint (map A e) @ (adjoint (map A e') @ t0)) ~
    map t ([map_comp A e e'] @ (adjoint (map A e) @ (adjoint (map A e') @ t0))). 
  apply equiv_eq_nat_trans. red. red.  simpl. 
  match goal with | [ |- sigma (λ α : ?H, _)]
                    => assert H end. 
  intro. Transparent Equiv_adjoint. simpl. unfold id. Opaque Equiv_adjoint. 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  apply (map2 t). trunc1_eq_expl (A @ z).
  exists X. red; intros. simpl. 
  pose (tt0 := t @ ([map A e' ° map A e] @
        (adjoint (map A e) @ (adjoint (map A e') @ t0)))).
  trunc1_eq_expl tt0.
Defined. 

Definition fun_eq_compT {Γ : [Type0]} (A: [ [[Γ]] --> Type0 ])  (x y z :[Γ])
           (e : x ~1 y) (e' : y ~1 z) :
           Equiv_eq (fun_eqT (map A (e' ° e)) (@identity _ _ _Type_id Type0))
                    (fun_eqT (map A e') (@identity _ _ _Type_id Type0) ° fun_eqT (map A e) (@identity _ _ _Type_id Type0)) := (fun_eq_map' A x y z e e' ; _).
Next Obligation. 
  intro. intro. apply equiv_eq_nat_trans. 
  Opaque composition. simpl. red. 
  match goal with | [ |- sigma (λ α : ?H, _)]
                    => assert H end.
  intro. Transparent composition. simpl.
  unfold id. eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t). apply inverse.
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). apply Equiv_adjoint_map_comp. 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply inverse. apply (map_comp t).
  apply (map2 t). trunc1_eq_expl (A @ z).
  exists X. red; intros. trunc1_eq (t @ t0).
Defined.


Definition Equiv_adjoint_map2 {Γ : [Type0]} (A: [ [[Γ]] --> Type0 ]) (x y :[Γ])
           (e e' : x ~1 y) (X : e ~2 e') t t0
           (H := fun_eq_eq (map2 A X) (identity (identity (|Type0|g))) :
          [fun_eqT (map A e) (@identity _ _ _Type_id Type0)] ~1
          [fun_eqT (map A e') (@identity _ _ _Type_id Type0)]) :
  (Equiv_adjoint H @ t) @ (adjoint (map A e') @ t0) ~
  map t ([map2 A X] @ (adjoint (map A e') @ t0)). 
  apply equiv_eq_nat_trans. red. red.  simpl. 
  match goal with | [ |- sigma (λ α : ?H, _)]
                    => assert H end. 
  intro. Transparent Equiv_adjoint. simpl. unfold id. Opaque Equiv_adjoint. 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  apply (map2 t). trunc1_eq_expl (A @ y).
  exists X0. red; intros. pose (tt0 := t @ ([map A e'] @ (adjoint (map A e') @ t0))).
  trunc1_eq_expl tt0.
Defined.

Definition fun_eq_map2T {Γ : [Type0]} (A: [ [[Γ]] --> Type0 ]) (x y :[Γ])
           (e e' : x ~1 y) (X : e ~2 e') :
         Equiv_eq (fun_eqT (map A e) (@identity _ _ _Type_id Type0))
                  (fun_eqT (map A e') (@identity _ _ _Type_id Type0)) :=
  (fun_eq_eq (map2 A X) (identity (identity (|Type0|g))); _).
Next Obligation. 
  intro. intro. apply equiv_eq_nat_trans. 
  Opaque composition. simpl. red. 
  match goal with | [ |- sigma (λ α : ?H, _)]
                    => assert H end.
  intro. Transparent composition. simpl.
  unfold id. eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t). apply inverse.
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). eapply inverse. apply (map_inv t). 
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply (map [map t _]). apply Equiv_adjoint_map2.
  eapply composition. eapply inverse. apply (map_comp t).
  eapply composition. eapply inverse. apply (map_comp t).
  apply (map2 t). trunc1_eq_expl (A @ y).
  exists X0. red; intros. trunc1_eq (t @ t0).
Defined.


Program Definition fun_eq_id2 {Γ : UGroupoidType} (A B:  [Γ --> _Type]) (x : [Γ]) :
  fun_eq (map A (identity x)) (map B (identity x)) ~1
  identity _.
eapply composition. apply fun_eq_eq. 
apply (map_id A). apply (map_id B).
unfold fun_eq. eapply composition. apply nat_comp'. apply left_comp_id. 
apply right_comp_id. apply nat_id_L. Defined.
