(* Add LoadPath "." as Groupoid. *)
Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Require Import Groupoid.groupoid.
Require Import Groupoid.fun_eq.
Require Import Groupoid.groupoid_interpretation_def.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Program Mode.
Set Primitive Projections.

Opaque Equiv_adjoint.
Opaque map_inv.

Definition equiv_adjoint {Γ:Context} {A:Typ Γ} (a:Elt A) 
        {x y : [Γ]} (e : x ~1 y) : a @ x ~1 (adjoint (map A e)) @ (a @ y) :=
  (map (adjoint (map A e)) (Dmap a e)) ° [inverse (retraction (map A e))] (a @ x).

Definition Equiv_adjoint_comp {Γ:Context} {A:Typ Γ} (a:Elt A) (x y z:[Γ]) (e:x~1 y) (e': y ~1 z):
[Equiv_adjoint [map_comp A e e'] ] ([a] z) ° equiv_adjoint a (e' ° e) ~
   map (adjoint (map A e)) (equiv_adjoint a e') ° equiv_adjoint a e.
apply Trunc_1. 
Defined. 

Definition Equiv_adjoint_eq {Γ:Context} {A:Typ Γ} (a:Elt A) (x y:[Γ]) (e e':x~1 y) (E: e ~ e'):
[Equiv_adjoint [map2 A E] ] ([a] y) ° equiv_adjoint a e ~
   equiv_adjoint a e'.
  apply Trunc_1. 
  (* unfold equiv_adjoint. simpl. eapply composition. apply comp. *)

  (* apply identity. apply (Equiv_adjoint_simpl _ _[(map2 A) E]). *)
  (* simpl. *)
  (* apply comp. eapply composition. eapply inv. apply (eq_retraction (map2 A E)).  *)
  (* simpl. eapply composition. eapply inverse. (* apply comp_inv. apply comp. apply identity. *) *)
  (* apply inverse, comp_inv.  *)
  (* eapply composition. apply @_map2. apply (Dmap2 a E). apply _map_comp. apply identity. *)
  (* simpl.  *)
Defined.

Definition Equiv_adjoint_identity {Γ:Context} {A:Typ Γ} (a:Elt A) (x:[Γ]) : 
  [Equiv_adjoint [map_id A] ] (a @ x) ° equiv_adjoint a (identity x) ~
   identity ([a] x).
  (* trunc1_eq. *)
  unfold equiv_adjoint. simpl. eapply composition. apply comp.
  apply comp. eapply composition. apply inv. apply (eq_retraction (map_id A)).
  simpl. simpl_id'. eapply (map2 (adjoint (map A (identity x)))). apply (Dmap_id a). apply identity.
  eapply composition. apply comp.
  eapply composition. eapply comp. eapply inverse.
  apply (comp_inv _ _ _ _ (Equiv_adjoint [map_id A] @ ([map A (identity x)] @ (a @ x)))).
  apply identity.
  eapply composition. eapply inverse. apply assoc. eapply composition. apply comp. apply identity.
  eapply inverse.
  exact (α_map (inverse (Equiv_adjoint [map_id A ])) ([map_id ([[[A]]])] @ ([a] x))).
  eapply composition. apply assoc. apply comp.  apply inv_R. apply identity. apply identity. simpl_id'. apply inv_R.
Defined.

Definition equiv_adjoint_map (Γ: Context) (A : Typ Γ)  (γ γ' : [Γ]) (e0 : γ ~1 γ')
        (x y : Elt A) (e : x ~1 y) : 
   map (adjoint (map A e0)) ([e] γ') ° equiv_adjoint x e0 ~
   equiv_adjoint y e0 ° [e] γ.
  apply Trunc_1. 
Defined.
