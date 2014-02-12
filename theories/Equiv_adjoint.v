Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
(* Add Rec LoadPath "." as Groupoid. *)
Require Import groupoid.
Require Import fun_eq.
Require Import groupoid_interpretation_def.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Program Mode.
Set Primitive Projections.

Opaque Equiv_adjoint.
Opaque map_id map_inv.

Definition equiv_adjoint {Γ:Context} {A:Typ Γ} (a:Elt A) 
        {x y : [Γ]} (e : x ~1 y) : a @ x ~1 (adjoint (map A e)) @ (a @ y) :=
  (map (adjoint (map A e)) (Dmap a e)) ° [inverse (retraction (map A e))] (a @ x).

Definition Equiv_adjoint_comp {Γ:Context} {A:Typ Γ} (a:Elt A) (x y z:[Γ]) (e:x~1 y) (e': y ~1 z):
[Equiv_adjoint [map_comp A e e'] ] ([a] z) ° equiv_adjoint a (e' ° e) ~
   map (adjoint (map A e)) (equiv_adjoint a e') ° equiv_adjoint a e.
unfold equiv_adjoint. simpl.
eapply composition. apply comp. apply comp. apply identity.
eapply composition. eapply (map2 (adjoint (map A (e' ° e)))). eapply (Dmap_comp a).
eapply composition.
apply (map_comp (adjoint (map A (e' ° e)))). apply comp. apply identity. apply (map_comp(adjoint (map A (e' ° e)))). apply identity.
(* unfold map; simpl. *)
eapply composition. apply comp. apply identity.
apply (Equiv_adjoint_simpl [map_comp A e e']). simpl. simpl_id.
unfold inverse. 
Admitted.

Definition Equiv_adjoint_eq {Γ:Context} {A:Typ Γ} (a:Elt A) (x y:[Γ]) (e e':x~1 y) (E: e ~ e'):
[Equiv_adjoint [map2 A E] ] ([a] y) ° equiv_adjoint a e ~
   equiv_adjoint a e'.
  unfold equiv_adjoint. simpl. eapply composition. apply comp.
  apply comp. eapply composition. eapply inv. apply (eq_retraction (map2 A E)). 
  simpl. eapply composition. eapply inverse. (* apply comp_inv. apply comp. apply identity. *)
  (* apply inverse, comp_inv.  *)
  (* eapply composition. apply @_map2. apply (Dmap2 a E). apply _map_comp. apply identity. *)
  (* simpl.  *)
Admitted.

Transparent map_id.
Definition map_id_Type0 Γ (A:[Γ --> |Type0|g]) (γ:[Γ]) (x : [A @ γ]) : [map_id (Type0_Type A)] @ x = [map_id A] @ x.
  simpl. apply eq_refl.
Defined.
Opaque map_id.

Definition Equiv_adjoint_identity {Γ:Context} {A:Typ Γ} (a:Elt A) (x:[Γ]) : 
  [Equiv_adjoint [map_id A] ] (a @ x) ° equiv_adjoint a (identity x) ~
   identity ([a] x).
  unfold equiv_adjoint. simpl. eapply composition. apply comp.
  apply comp. eapply composition. apply inv. apply (eq_retraction (map_id A)). 
  simpl. simpl_id. eapply (map2 (adjoint (map A (identity x)))). apply (Dmap_id a). apply identity.
  eapply composition. apply comp.
  eapply composition. eapply comp. eapply inverse. 
  apply (comp_inv _ _ _ (Equiv_adjoint [map_id A] @ ([map A (identity x)] @ (a @ x)))).
  apply identity. 
  eapply composition. eapply inverse. apply assoc. eapply composition. apply comp. apply identity. 
  eapply inverse.
  exact (α_map (inverse (Equiv_adjoint [map_id A ])) ([map_id ([[[A]]])] @ ([a] x))). 
  eapply composition. apply assoc. apply comp. rewrite map_id_Type0. apply inv_R. apply identity. apply identity. simpl_id. apply inv_R.
Defined.

Definition equiv_adjoint_map (Γ: Context) (A : Typ Γ)  (γ γ' : [Γ]) (e0 : γ ~1 γ')
        (x y : Elt A) (e : x ~1 y) : 
   map (adjoint (map A e0)) ([e] γ') ° equiv_adjoint x e0 ~
   equiv_adjoint y e0 ° [e] γ.
Admitted.
