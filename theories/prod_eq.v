Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Add Rec LoadPath "." as Groupoid.
Require Import HoTT_light.
Require Import groupoid.
Require Import fun_eq.
Require Import groupoid_interpretation_def.
Require Import Equiv_adjoint.
Require Import fun_depfun.

Set Implicit Arguments.
Set Program Mode.
Set Primitive Projections.
 
Opaque Equiv_adjoint.
Opaque map_id map_inv.

(* An other version of prod_eq *)

Program Definition Prod_eq_ {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y) : 
  [F] x ° adjoint (map A e) ~ [F] y 
  := Dmap F e ° inverse (nat_id_L ([F] x ° adjoint (map A e))).

Program Definition Prod_eq_1 {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y)
        (X: Prod_Type (F @ x)) (a : [A @ y]) : [(F@ y) @ a] :=
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

(* Definition map_comp' {T U} (f:T ---> U) {x y z: [T]} (e: x ~1 y) (e':y ~1 z) := *)
(*   (proj2 f).(_map_comp)  e e' : map f (e' ° e) ~ map f e' ° map f e. *)

Definition map_comp' {T U} (f:T ---> U) {x y z: [T]} (e: x ~1 y) (e':y ~1 z) :=
  _map_comp (WeakFunctor := proj2 f) e e' : map f (e' ° e) ~ map f e' ° map f e.

Next Obligation. intro. intros. simpl. refine (map_comp' _ _ _). Defined.

Next Obligation. simpl; red; intros; simpl. apply (_map2 (X _)). Defined.

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


