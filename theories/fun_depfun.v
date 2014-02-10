Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
(* Add Rec LoadPath "." as Groupoid. *)
Require Import HoTT_light.
Require Import groupoid.
Require Import fun_eq.
Require Import groupoid_interpretation_def.
Require Import Equiv_adjoint.

Set Implicit Arguments.
Set Program Mode.
Set Primitive Projections.
 
Opaque Equiv_adjoint.
Opaque map_id map_inv.


Instance comp_fun_depfun_1  {T T': Context} {U : [ [[T']] --> _Type]}
        (F : [ T -|-> T' ]) (G : [_Prod U]) : DependentFunctor (U ⋅ F) (λ x : [T], G @ (F @ x)).
Next Obligation. apply (Dmap G (map F e)). Defined.
Next Obligation. admit. Defined.
Next Obligation. unfold comp_fun_depfun_1_obligation_1. 
                 eapply composition. apply (Dmap2 G (map_comp F e e')).
                 eapply composition. apply comp. apply identity. 
                 apply (Dmap_comp G). eapply composition. apply assoc. 
                 apply identity.
                 Defined.
Next Obligation. apply (Dmap2 G (map2 F H)). Defined. 

Program Definition comp_fun_depfun {T T': Context} {U : [ [[T']] --> _Type]}
        (F : [ T -|-> T' ]) (G : [_Prod U]) : [_Prod (U ⋅ F)] :=
(λ x : [T], G @ (F @ x); comp_fun_depfun_1 _ _ ).

Notation  "g '°°' f" := (comp_fun_depfun f g) (at level 50). 
