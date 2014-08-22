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


Instance comp_fun_depfun_1  {T T': Context} {U : [ [[T']] --> _Type]}
        (F : [ T -|-> T' ]) (G : [_Prod U]) : DependentFunctor (U ⋅ F) (λ x : [T], G @ (F @ x)).
Next Obligation. apply (Dmap G (map F e)). Defined.
Next Obligation. eapply composition. apply (Dmap2 G (map_id F)).
                 apply comp. apply identity. apply (Dmap_id G).
Defined.
Next Obligation. eapply composition. apply (Dmap2 G (map_comp F e e')).
                 eapply composition. apply comp. apply identity. 
                 apply (Dmap_comp G). apply assoc. 
Defined.
Next Obligation. apply (Dmap2 G (map2 F H)). 
Defined. 

Program Definition comp_fun_depfun {T T': Context} {U : [ [[T']] --> _Type]}
        (F : [ T -|-> T' ]) (G : [_Prod U]) : [_Prod (U ⋅ F)] :=
(λ x : [T], G @ (F @ x); comp_fun_depfun_1 _ _ ).

Notation  "g '°°' f" := (comp_fun_depfun f g) (at level 50). 

Notation  "f '⋅⋅' σ" := (@action _ _ ActionType _ _  σ f) (at level 50).

Program Instance comp_fun_depfun0_1 {T T': Context} {U : [ [[T']] -||-> Type0]}
        (F : [ T -|-> T' ]) (G : [Prod0 U]) : 
                                     DependentFunctor ([[[U ⋅⋅ F]]]) (λ x : [T], G @ (F @ x)).
Next Obligation. intros. apply (Dmap G (map F e)). Defined.
Next Obligation. eapply composition. apply (Dmap2 G (map_id F)).
                 apply comp. apply identity. apply (Dmap_id G).
Defined.
Next Obligation. eapply composition. apply (Dmap2 G (map_comp F e e')).
                 eapply composition. apply comp. apply identity. 
                 apply (Dmap_comp G). apply assoc. 
Defined. 
Next Obligation. apply (Dmap2 G (map2 F H)). 
Defined. 

Program Definition comp_fun_depfun0 {T T': Context} {U : [ [[T']] -||-> Type0]}
        (F : [ T -|-> T' ]) (G : [Prod0 U]) : [Prod0 (U ⋅⋅ F)] :=
(λ x : [T], G @ (F @ x); comp_fun_depfun0_1 _ _).

Notation  "g '°°°°' f" := (comp_fun_depfun0 f g) (at level 50). 
