Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Add LoadPath "." as Groupoid.
Require Import Groupoid.HoTT_light.
Require Import Groupoid.groupoid.
Require Import Groupoid.fun_eq.
Require Import Groupoid.groupoid_interpretation_def.
Require Import Groupoid.Equiv_adjoint.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Program Mode.
Set Primitive Projections.

Opaque Equiv_adjoint.
Opaque map_inv.

Definition ext (Γ: Context) (T : Typ Γ) : Type := sigma (fun γ => [T @ γ]).

Definition cons {Γ: Context} {T : Typ Γ} (γ : [Γ]) (x : [T @ γ]) : ext T := (γ;x).

Definition sum_id_left {Γ: Context} {T : Typ Γ} 
        {γ : [Γ]} {x y : [T @ γ]}  (e : x ~1 y) : (cons γ x) ~1 (cons γ y)
 := (identity _ ; e ° ([map_id T] @ x)).

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
exists (identity _). simpl. unfold transport_id, transport_eq.
eapply composition. apply id_L. eapply inverse. eapply composition; try apply id_R.
apply comp. apply (map2_id T _ x). apply identity.
Defined.

Definition sum_eq_map {Γ: Context} {T : Typ Γ}
        (x y : [Γ]) (X : x ~1 y) (t : [T @ y]) :
  (x;transport ([[[T]]]) (inverse X) @ t) ~1 (y;t).
  exists X. simpl. unfold eq_rect.
  eapply composition;
    try apply (section (map T X) @ t).
  exact ([comp _ _ _ _ _ _ _
                     (map_inv T _ _ X) (identity _)] @ t).
Defined.

Definition sum_id_right {Γ} {A:Typ Γ} {γ γ' : [Γ]}
  (e : γ ~1 γ') (a' : [A @ γ']) : (cons γ (adjoint (map A e) @ a')) ~1 (cons γ' a').
exists e. apply ((section (map A e)) @ a'). 
Defined.

Definition sum_eq_map' {Γ: Context} {T : Typ Γ}
        (x y : [Γ]) (X : x ~1 y) (x0 y0 : [T @ y]) (e : x0 ~1 y0):
  (x;transport ([[[T]]]) (inverse X) @ x0) ~1 (y;y0).
  exists X. simpl. unfold eq_rect.
  eapply composition;
    try apply (section (map T X) @ y0).
  eapply composition.
  exact ([comp _ _ _ _ _ _ _
                     (map_inv T _ _ X) (identity _)] @ x0).
  pose (foo := map [map T X] (map [inverse (map T X)] e)).
  apply foo.
Defined.

(* Definition map2_id_R_L {Γ: Context} {A : Typ Γ} *)
(*  (x y : [Γ]) (e : x ~1 y) :(id_L x y e) ^-1 ° id_R x y e ~ identity _. *)
(*   map2 A ( (id_L x y e) ^-1 ° id_ x y e) ~ identity _. *)

Definition sum_id_left_right {Γ: Context} {A : Typ Γ}
 (x y : [Γ]) (e : x ~1 y) (t t' : [ [A] y]) (e' : t ~1 t'):
  sum_id_left e' ° sum_id_right e t ~
  sum_id_right e t' ° sum_id_left (map (adjoint (map A e)) e').
  exists (inverse  (id_R _ _ _) ° id_L _ y e). simpl.
  trunc1_eq.
Defined.
