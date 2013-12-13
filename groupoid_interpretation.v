(** printing ~1 $\sim_1$ *)
(** printing ~ $\sim_2$ *)
(** printing ~2 $\sim_2$ *)
(** printing Π1 $\pi_1$*)
(** printing Π2 $\pi_2$*)
(** printing Πi $\pi_i$*)
(** printing --> $\longrightarrow$*)
(** printing ---> $\longrightarrow$*)
(** printing β $\beta$*)
(** printing γ $\gamma$*)
(** printing Γ $\Gamma$*)
(** printing γt $\gamma t$*)
(** printing Δ $\Delta$*)
(** printing χ $\chi$*)
(** printing [! $\llbracket$*)
(** printing !] $\rrbracket$*)
(** printing |- $\vdash$*)
(** printing === $\equiv$*)
(** printing <--> $\Leftrightarrow$*)
(** printing @ $\star$*)
(** printing @@ $\star$*)
(** printing ° $\circ$*)
(** printing °° $\circ$*)
(** printing °°° $\circ$*)
(** printing Category_1 $\mathrm{Category}_1$*)
(** printing Category_2 $\mathrm{Category}_2$*)
(** printing CategoryP $\mathrm{Category}$*)
(** printing GroupoidP $\mathrm{Groupoid}$*)
(** printing Groupoid_1 $\mathrm{Groupoid}_1$*)
(** printing Groupoid_2 $\mathrm{Groupoid}_2$*)
(** printing Equivalence_2 $\mathrm{Equivalence}_2$*)
(** printing Hom1 $\mathrm{Hom}_1$*)
(** printing Hom2 $\mathrm{Hom}_2$*)
(** printing Hom3 $\mathrm{Hom}_3$*)
(** printing _adjoint $\mathrm{adjoint}$*)
(** printing _section $\mathrm{section}$*)
(** printing _retraction $\mathrm{retraction}$*)
(** printing _triangle $\mathrm{triangle}$*)
(** printing nat_comp' $\mathrm{comp}$*)
(** printing _α_map $\mathrm{α}_\mathrm{map}$*)
(** printing _α_Dmap $\mathrm{α}_{\mathrm{map}^\Pi}$*)
(** printing α_map $\mathrm{α}_\mathrm{map}$*)
(** printing α_Dmap $\mathrm{α}_{\mathrm{map}^\Pi}$*)
(** printing _eq_section $\mathrm{eq\_section}$*)
(** printing _eq_retraction $\mathrm{eq\_retraction}$*)
(** printing Prod_Type $\Pi_\mathrm{T}$*)
(** printing _Prod $\Pi$*)
(** printing _Sum $\Sigma$*)
(** printing sum_type $\Sigma_\mathrm{T}$*)
(** printing sum_eq $\Sigma_\mathrm{Eq}$*)
(** printing sum_eq2 $\Sigma_{\mathrm{Eq}_2}$*)
(** printing eq2 $\mathrm{eq}_2$*)
(** printing eq1 $\mathrm{eq}_1$*)
(** printing HomT2 $\mathrm{HomT}_2$*)
(** printing HomT1 $\mathrm{HomT}_1$*)
(** printing id_R $\mathrm{id}_R$*)
(** printing id_L $\mathrm{id}_L$*)
(** printing inv_R $\mathrm{inv}_R$*)
(** printing inv_L $\mathrm{inv}_L$*)
(** printing ^-1 $\hspace{-1ex}^{-1}$*)
(** printing Trunc_2 $\mathrm{Trunc}_2$*)
(** printing map_id $\mathrm{map}_\mathrm{id}$*)
(** printing map_comp $\mathrm{map}_\mathrm{comp}$*)
(** printing map2 $\mathrm{map}_2$*)
(** printing _map $\mathrm{map}$*)
(** printing _map_id $\mathrm{map}_\mathrm{id}$*)
(** printing _map_comp $\mathrm{map}_\mathrm{comp}$*)
(** printing _map2 $\mathrm{map}_2$*)
(** printing map1 $\mathrm{map}_1$*)
(** printing Dmap $\mathrm{map}^\Pi$*)
(** printing _Dmap $\mathrm{map}^\Pi$*)
(** printing Dmap_id $\mathrm{map}^\Pi_\mathrm{id}$*)
(** printing Dmap_comp $\mathrm{map}^\Pi_\mathrm{comp}$*)
(** printing Dmap2 $\mathrm{map}^\Pi_2$*)
(** printing _Dmap_id $\mathrm{map}^\Pi_\mathrm{id}$*)
(** printing _Dmap_comp $\mathrm{map}^\Pi_\mathrm{comp}$*)
(** printing _Dmap2 $\mathrm{map}^\Pi_2$*)
(** printing Dmap1 $\mathrm{map}^\Pi_1$*)
(** printing DependentFunctor $\mathrm{Functor}^\Pi$*)
(** printing WeakDependentFunctor $\mathrm{WeakFunctor}^\Pi$*)
(** printing DNaturalTransformation $\mathrm{NaturalTransformation}^\Pi$*)
(** printing Dnat_trans $\mathrm{nat\_trans}^\Pi$*)
(** printing Dmodification $\mathrm{modification}^\Pi$*)
(** printing WeakDependentFunctor $\mathrm{WeakFunctor}^\Pi$*)
(** printing DNaturalTransformation $\mathrm{NaturalTransformation}^\Pi$*)
(** printing Dnat_trans $\mathrm{nat\_trans}^\Pi$*)
(** printing Dmodification $\mathrm{modification}^\Pi$*)
(** printing WeakGroupoidType $\mathrm{WeakGroupoidT}$*)
(** printing sum_weakgroupoid $\Sigma_\mathrm{WG}$*)
(** printing prod_weakgroupoid $\Pi_\mathrm{WG}$*)
(** printing IrrRelWeakGroupoid $\mathrm{IrrRelWG}$*)
(** printing Hom_irr $\mathrm{HomIrr}$*)


(* begin hide *)

Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
(* Require Import Setoid. *)
Add Rec LoadPath ".".
Require Import groupoid.
Require Import groupoid_utility.
Require Import groupoid_interpretation_def.
Require Import groupoid_utility2.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Program Mode.
Set Primitive Projections.

(** These are indexed for type class resolution *)
Typeclasses Opaque Hom_irr sum_eq sum_eq2 nat_trans modification 
            Dnat_trans Dmodification Equiv_eq Equiv_eq2.

Hint Extern 0 (@Inverse _ (@eq2 (@Hom2 (@WC (proj2 _Type))) _ _)) =>
  exact (Inv_Equiv_eq _ _) : typeclass_instances.
Hint Extern 0 (@Composition _ (@eq2 (@Hom2 (@WC (proj2 _Type))) _ _)) =>
  exact (Comp_Equiv_eq _ _) : typeclass_instances.
Hint Extern 0 (@Identity _ (@eq2 (@Hom2 (@WC (proj2 _Type))) _ _)) =>
  exact (Id_Equiv_eq _ _) : typeclass_instances.
 
Opaque Equiv_adjoint.
Obligation Tactic := simpl; intros.

Definition curry {Γ: Context} {T : Typ Γ} (U : TypDep T) (γ : [Γ]) :=
  λ t : [T @ γ], U @ (γ; t).

Instance Curry1 {Γ: Context} {T : Typ Γ}
        (U : TypDep T) (γ : [Γ]) : WeakFunctor (curry U γ).
Next Obligation. exact (map U (sum_id_left X)). Defined.
Next Obligation. 
  eapply composition. apply (map2 U (inverse (sum_id_left_comp _ _ _ _ e e'))).
  apply (map_comp U).
Defined.
Next Obligation.
  apply (map2 U). apply sum_id_left_map. exact X.
Defined.

Definition Curry {Γ: Context} {T : Typ Γ}
        (U : TypDep T) (γ : [Γ]) : [T @ γ --> _Type] :=
  (curry U γ ; _). 

Definition Family {Γ: Context} (A : Typ Γ) :=
  (λ s : [Γ], [A] s --> _Type; TypFam_1 A).

Instance LamT_1 {Γ: Context} {A : Typ Γ} (B: Typ (_Sum A)) :
  WeakDependentFunctor (Family A) (Curry B).

Obligation Tactic := idtac.
Next Obligation. intros. exists (fun a => map B (sum_id_right e a)).
                 econstructor. intros. 
                 eapply composition. eapply inverse. apply (map_comp B).
                 eapply composition. Focus 2. apply (map_comp B).
                 apply (map2 B). apply inverse, sum_id_left_right. Defined.

Opaque _Type.

Lemma all_id_R (W : WeakGroupoidType) (x : [W]) (f g : x ~1 x) : 
  (f ~ identity x) -> (g ~ identity x) -> (f ° g ~ identity x).
Proof.
  intros. eapply composition. apply comp. apply X0. apply X. apply comp_id. 
Qed.
Lemma all_id_inv (W : WeakGroupoidType) (x : [W]) (f : x ~1 x) : 
  (f ~ identity x) -> (f ^-1 ~ identity x).
Proof.
  intros. eapply composition. apply inv. apply X. apply inv_id. 
Qed.

(* Ltac all_id := try apply (@all_id_R _); repeat *)
(*   match goal with  *)
(*       |- @eq2 (eq_pi4' ?type) _ _ (_ ° _) (identity _) =>  *)
(*       apply (@all_id_R type) *)
(*     | |- @eq2 (eq_pi4' ?type) _ _ (_ ^-1) (identity _) =>  *)
(*       apply (@all_id_inv type) *)
(*     | |- @eq2 (eq_pi4' ?type) _ _ (identity _) (identity _) =>  *)
(*       apply identity *)
(*   end. *)
Ltac simpl_id_end ::= 
  match goal with
    | [ |- eq2 (?P ^-1 ° ?P) _] => compose;
       [first [apply equiv_inv_L|apply inv_L]|idtac]
    | [ |- eq2 (?P ° ?P ^-1) _] => compose;
       [first [apply equiv_inv_R|apply inv_R]|idtac]
    | [ |- eq2 (?P ° identity ?x) _] => compose;
       [first [apply equiv_id_R|apply id_R]|idtac]
    | [ |- eq2 (identity ?x ° ?P) _] => compose;
       [first [apply equiv_id_L | apply id_L]|idtac]
    | [ |- eq2 ((?P ^-1) ^-1) _] => compose;
       [first [apply (@inv_inv _Type)|apply inv_inv]|idtac]
    | [ |- eq2 ((identity _) ^-1) _] => compose;
       [first [apply (@inv_id _Type)|apply inv_id]|idtac]
    | [ |- Equiv_eq (?P ^-1 ° ?P) _] => compose; [apply equiv_inv_L|idtac]
    | [ |- Equiv_eq (?P ° ?P ^-1) _] => compose; [apply equiv_inv_R|idtac]
    | [ |- Equiv_eq (?P ° identity ?x) _] => compose; [apply equiv_id_R|idtac]
    | [ |- Equiv_eq (identity ?x ° ?P) _] => compose; [apply equiv_id_L|idtac]
    | [ |- Equiv_eq ((?P ^-1) ^-1) _] => compose; [apply (@inv_inv _Type)|idtac]
    | [ |- Equiv_eq ((identity _) ^-1) _] => compose; [apply (@inv_id _Type)|idtac]
  end.


Ltac simpl_id_end_extended ::= first [ simpl_id_end |
                                      match goal with
                   | [ |- Equiv_eq ?e _ ] => apply (identity e)
                   | [ |- eq2 ?e _ ] => apply (identity e)
                   | [ |- _ ] => idtac
                 end].

Ltac simpl_id ::= first [simpl_id_end ; simpl_id |
  lazymatch goal with
    | |- context [identity _] => fail
    | |- _ => apply identity
  end|
  lazymatch goal with
  | [ |- eq2 (?P ^-1) _] => eapply composition;
                           [first [apply equiv_inv | apply inv] ; simpl_id | idtac]; 
                           try apply identity
  | [ |- eq2 (map ?F (identity _)) _] => eapply composition;
                                        [eapply (map_id F); simpl_id | idtac]; 
                                        simpl_id
  | [ |- Equiv_eq (map ?F (identity _)) _] => eapply composition;
                                             [eapply (map_id F); simpl_id | idtac]; 
                                             simpl_id
  | [ |- eq2 (map ?F ?P) _] => first [eapply composition;
                                       [eapply (map2 F); simpl_id | idtac]; 
                                       [apply identity | idtac] | 
                                      (progress_evars (eapply composition;
                                                       [eapply (map2 F); simpl_id | idtac];instantiate));
                                        simpl_id |idtac]
  | [ |- Equiv_eq (map ?F ?P) _] => 
    first [eapply composition;
            [eapply (map2 F); simpl_id | idtac]; 
            [apply identity | idtac] | 
           (progress_evars (eapply composition;
                            [eapply (map2 F); simpl_id | idtac];instantiate));
             simpl_id |idtac]
  | [ |- Equiv_eq (?P ^-1) _] =>
    eapply composition;
      [apply equiv_inv; simpl_id | idtac]; 
      try apply identity
  | [ |- Equiv_eq (?Q ° ?P) _] => 
    eapply composition;
      [apply equiv_comp ; simpl_id | idtac];
      simpl_id_end_extended
  | [ |- Equiv_eq ?e _ ] => apply (identity e)
  | [ |- eq2 (?Q ° ?P) _] =>
    eapply composition;
      [first [apply equiv_comp 
             | apply comp] ; simpl_id | idtac];
      simpl_id_end_extended
  | [ |- eq2 ?e _ ] => first [has_evar e; idtac | apply (identity e)]
  | [ |- _ ] => idtac
                         end].

Ltac simpl_id_bi ::= simpl_id; eapply inverse; simpl_id.

(* Ltac simpl_id_end ::=  *)
(*   match goal with *)
(*     | |- (@eq2 _ _ _ _ (identity _)) => all_id *)
(*     | |- (@Equiv_eq _ _ _ (identity _)) => all_id *)
(*     | |- (@eq2 _ _ _ _ ?R) => try (not_evar R; eapply composition) *)
(*     | |- (@Equiv_eq _ _ _ ?R) => try (not_evar R; eapply composition) *)
(*   end; *)
(*   [match goal with *)
(*      | [ |- eq2 (?P ^-1 ° ?P) _] =>  *)
(*        first [apply inv_L | apply equiv_inv_L] *)
(*      | [ |- eq2 (?P ° ?P ^-1) _] =>  *)
(*        first [apply inv_R | apply equiv_inv_R] *)
(*      | [ |- eq2 (?P ° identity ?x) _] =>  *)
(*        first [apply id_R | apply equiv_id_R] *)
(*      | [ |- eq2 (identity ?x ° ?P) _] =>  *)
(*        first [apply id_L | apply equiv_id_L] *)
(*      | [ |- eq2 ((?P ^-1) ^-1) _] =>  *)
(*        first [apply inv_inv | apply (@inv_inv _Type)] *)
(*      | [ |- eq2 ((identity _) ^-1) _] =>  *)
(*        first [apply inv_id | apply (@inv_id _Type)] *)
(*      | [ |- Equiv_eq (?P ^-1 ° ?P) _] => apply equiv_inv_L *)
(*      | [ |- Equiv_eq (?P ° ?P ^-1) _] => apply equiv_inv_R *)
(*      | [ |- Equiv_eq (?P ° identity ?x) _] => apply equiv_id_R *)
(*      | [ |- Equiv_eq (identity ?x ° ?P) _] => apply equiv_id_L *)
(*      | [ |- Equiv_eq ((?P ^-1) ^-1) _] => apply (@inv_inv _Type) *)
(*      | [ |- Equiv_eq ((identity _) ^-1) _] => apply (@inv_id _Type) *)
(*    end |idtac ..]. *)

Transparent _Type.
  
Ltac mysimpl := 
  cbn beta iota zeta delta -[_Type curry]. 
Unset Printing All.

Next Obligation. 
  intros. unfold LamT_1_obligation_1. intro. mysimpl. Opaque _Type.
  Transparent _Type.
  Time eapply inverse. 
  Time simpl_id. Time simpl_id.
  eapply composition; [apply equiv_comp|idtac].
  mysimpl.
  Time apply identity.
  Time eapply inverse.
  apply (map_comp B).
  eapply composition. eapply inverse. apply (map_comp B).
  apply (map2 B).
  assert (((sum_id_right e' t ° sum_id_right e ([adjoint (map A e')] t))
             ° sum_id_left ([Equiv_adjoint [map_comp A e e']] t)) ~
                                                                  (sum_id_right (e' ° e) t)).
  admit.
  exact X.
Defined.

Next Obligation. 
Proof. 
  intros. unfold LamT_1_obligation_1. intro. mysimpl. unfold Curry1_obligation_1.
  apply inverse. simpl_id.
  eapply composition. eapply inverse.
  apply (map_comp B). apply (map2 B).
  exists (inverse H ° id_R _ _ _). simpl. 
  unfold eq_rect_eq, eq_rect_comp. simpl_id_bi.
  eapply composition. apply comp. apply identity.
  apply (eq_section (map2 A H)). simpl.
  eapply composition. apply assoc.
  eapply inverse.
  eapply composition. apply assoc.
  apply comp; [idtac | apply identity].
  eapply composition. apply comp. apply identity.
  apply _map_comp. eapply composition. apply assoc.
  eapply inverse.
  eapply composition. apply assoc.
  apply comp; [idtac | apply identity].
  assert (map2 A H ° map2 A (inverse H ° id_R x y e') ~
               id_R _ _ _ ° (map_id A ** identity _) °  map_comp A (identity x) e').
  trunc_eq.
  eapply composition. apply X. 
  unfold HorComp. simpl. Transparent _Type. mysimpl.
  simpl_id. 
Defined.
(* end hide *)

(** 
  Elements of [TypDep A] and [TypFam A] can be related using a dependent closure
  at the level of types. In the interpretation of typing judgments, this connection 
  will be used to switch between the fibration and the morphism points of view.
  
*)
Obligation Tactic := intros.
Definition LamT {Γ: Context} {A : Typ Γ} (B: TypDep A)
  : TypFam A := (λ γ, (λ t, B @ (γ; t) ; Curry1 B γ); _).
Next Obligation. exact (LamT_1 B). Defined.

(* begin hide *)

Instance SubstT_1 {Γ:Context} {A:Typ Γ} (F:TypFam A) (a:Elt A) :
 WeakFunctor (λ s, (F @ s) @ (a @ s)).

Next Obligation. eapply composition; try apply ([Dmap F X] (a @ y)).
                 simpl. unfold id. apply (map (F @ x)).
                 apply equiv_adjoint.
Defined.

Tactic Notation "rapply" open_constr(f) := 
  first[refine (f _ _ _ _ _ _ _ _ _ _)|
        refine (f _ _ _ _ _ _ _ _ _)|
        refine (f _ _ _ _ _ _ _ _)|
        refine (f _ _ _ _ _ _ _ )|
        refine (f _ _ _ _ _ _ )|
        refine (f _ _ _ _ _)|
        refine (f _ _ _ _)|
        refine (f _ _ _ )|
        refine (f _ _)|
        refine (f _)].

Ltac mysimpl ::=
     cbn beta iota zeta delta -[_Type _Type_comp curry Equiv_cat _Equiv_Id eq_rect_comp].

Next Obligation.
Proof. 
  unfold SubstT_1_obligation_1.
  eapply composition. apply equiv_comp. apply identity.
  apply (Dmap_comp F e e' (a @ z)). 
  eapply composition.
  mysimpl.
  eapply equiv_assoc. eapply composition. eapply equiv_assoc.
  eapply inverse. eapply composition. apply equiv_assoc.
  apply equiv_comp; try apply identity.

  unfold eq_rect_comp. unfold _map_comp. Opaque _Type. simpl _map_comp.
  simpl proj1. cbn beta. Transparent _Type.
  unfold equiv_adjoint.
  apply inverse. simpl_id. simpl_id.
  mysimpl.
  
  eapply inverse. eapply composition. eapply inverse. apply equiv_assoc.
  eapply composition. apply equiv_comp. apply identity. eapply inverse.
  apply (α_map (Dmap F e)).
  Time eapply composition.
  Time eapply equiv_assoc.
  apply equiv_comp; [idtac | apply identity]. 
  eapply composition. eapply inverse. apply (map_comp (F @ x)).
  eapply inverse. eapply composition.
  eapply inverse.
  apply (map_comp (F @ x)).
  apply (map2 (F @ x)). apply Equiv_adjoint_comp.
Defined.

Next Obligation. 
Proof. 
  unfold SubstT_1_obligation_1.
  eapply composition. apply equiv_comp. apply identity.
  apply (Dmap2 F X (a @ y)).
  mysimpl. simpl_id.
  eapply composition. apply equiv_assoc.
  apply equiv_comp; [idtac | apply identity].
  eapply composition. eapply inverse. apply (map_comp (F @ x)).
  apply (map2 (F @ x)). apply Equiv_adjoint_eq.
Defined.
 
(* end hide *)

(** 

  ** Substitutions 

  A substitution is represented by a context morphism [[Γ --> Δ]]. 
  A substitution σ can be extended by an element [a: Elt (A ° σ)] 
  of [A : Typ Δ].

*)

(* begin hide *)

Instance SubExt_1 {Γ Δ : Context} {A : Typ Δ} (f: [Γ --> Δ]) (t: Elt (A ⋅ f)) : 
  WeakFunctor (λ s, (f @ s; t @ s) : [_Sum A]).
Next Obligation. exact (map f X; Dmap t X). Defined.
Next Obligation. exists (map_comp f e e'). simpl. 
                 eapply composition. exact (Dmap_comp t e e'). 
                 apply inverse. eapply composition. apply assoc. 
                 apply identity.
Defined.
Next Obligation. exact (map2 f X; Dmap2 t X). Defined.

(* end hide *)

Definition SubExt {Γ Δ : Context} {A : Typ Δ} (σ: [Γ --> Δ])
  (a: Elt (A ⋅ σ)) : [Γ --> (_Sum A)] := (λ γ, (σ @ γ; a @ γ) ; _).

(** %\noindent% where [_] is a proof that it is functorial. 
*)
(* begin hide *)

Arguments SubExt {Γ Δ A} σ a.

Instance SubExtId_1 {Γ : Context} {A : Typ Γ} (t: Elt (A)) : 
  WeakFunctor (λ s, (s; t @ s) : [_Sum A]).
Next Obligation. exact (X ; Dmap t X). Defined.
Next Obligation. exists (identity _). eapply composition.
                 exact (Dmap_comp t e e'). simpl. unfold eq_rect_eq.
                 eapply composition. Focus 2. apply comp. 
                 eapply inverse, map2_id. apply identity. simpl.
                 simpl_id_bi.
Defined.
Next Obligation. exact (X; Dmap2 t X). Defined.

Definition SubExtId {Γ : Context} {A : Typ Γ} 
 (t: Elt A) : [Γ --> (_Sum A)] := (λ γ, (γ; t @ γ) ; _).

Instance substF_1 {T Γ} {A:Typ Γ} (F:TypFam A) (f:[T --> Γ]) :
  WeakDependentFunctor (λ t : [T], (A ⋅ f) @ t --> _Type; TypFam_1 (A ⋅ f)) 
                       ([F °° f] : ∀ t : [T], (A ⋅ f) @ t ---> _Type).
Next Obligation. exact (Dmap F (map f e)). Defined.
Next Obligation. 
  intro. unfold substF_1_obligation_1. mysimpl.
  eapply inverse. unfold eq_rect_comp. 
  Opaque _Type. simpl proj1. cbn beta. Transparent _Type.
  simpl_id. simpl_id.
  apply inverse.
  eapply composition. apply (Dmap2 F (map_comp f e e') t).
  eapply composition. apply equiv_comp. apply identity.
  apply (Dmap_comp F (map f e) (map f e') t). mysimpl.
  unfold eq_rect_comp. 
  Opaque _Type. simpl proj1. cbn beta. Transparent _Type.
  simpl_id. simpl_id.
  eapply composition. apply equiv_assoc.
  eapply composition. apply equiv_assoc. apply inverse.
  eapply composition. apply equiv_assoc.
  apply equiv_comp; [idtac | apply identity].
  apply equiv_comp; [idtac | apply identity].
  apply inverse.
  eapply composition. 
  eapply inverse.
  apply (map_comp ([F] ([f] x))).
  apply (map2 ([F] ([f] x))).
  apply inverse. 
  apply (groupoid.Equiv_adjoint_comp [map2 A (map_comp f e e')]  [map_comp A (map f e) (map f e')] t). Defined.

Next Obligation. 
Proof. 
  intro. mysimpl. eapply composition. eapply (Dmap2 F (map2 f H) t).
  simpl_id_bi.
Defined.

Definition substF {T Γ} {A:Typ Γ} (F:TypFam A)
 (σ:[T --> Γ]) : TypFam (A ⋅ σ).
  do 3 red.
  simpl.
  exists [F °° σ]. (* Diverges apply _. *) apply (substF_1 _ _). Defined.

Notation  "F '°°°' σ " := (substF F σ) (at level 50).

(* end hide *)

(** A substitution [σ] can be applied to a type family [F] using the
  composition of a functor with a dependent functor. We
  abusively note all those different compositions with [°] as it is done in
  mathematics, whereas they are distinct operators in the %\Coq%
  development.

  The weakening substitution of $\Gamma, x:A \vdash$ is given by the first
  projection. 
*)

(* begin hide *)

Instance SubWeak_1 (Γ: [_Type]) (T : [Γ --> _Type])
         : WeakFunctor (λ γt : [_Sum T], [γt]).
Next Obligation. apply [X]. Defined.
Next Obligation. apply comp; apply identity. Defined.
Next Obligation. apply [X]. Defined.

(* end hide *)

Definition SubWeak {Γ: Context} {T : Typ Γ} : [_Sum T --> Γ] 
  :=  (λ γt:[_Sum T], [γt] ; _).


(** 
%\noindent%
  This substitution allows to interpret a type A in a weakened context 
  as [A ⋅ SubWeak]. This is noted  [⇑ A]. *)
(* begin hide *)
Notation "⇑ A" := (A ⋅ SubWeak) (at level 9, t at level 9).
(* end hide *)

(**
  
  A type family [F] in [TypFam A] can be partially substituted with an
  element [a] in [Elt A], noted [F {{ a }}], to get a type at [a]. 
  This process is defined as [F {{ a }} := (λ γ, (F @ γ) @ (a @ γ) ; _)] 
  (where [_] is a proof of that it is functorial). Note that this pattern of 
  application %\emph{up-to a context $\gamma$}% will be used later to defined 
  other notions of application. Although the computational definitions are the same,
  the compatibility conditions are always different. *)

(* begin hide *)

Definition SubstT {Γ:Context} {A:Typ Γ} (F:TypFam A) (a:Elt A) : Typ Γ :=
  (λ γ, (F @ γ) @ (a @ γ) ; _).
Obligation Tactic := idtac.

Transparent _Type.

Notation  "F '{{' a '}}'" := (SubstT F a) (at level 50).

(* end hide *)

(** This notion of partial substitution in a type family enables to state
 that [LamT] defines a type level $\lambda$-abstraction.

*)

Program Lemma BetaT {Δ Γ:Context}  {A:Typ Γ} (B:TypDep A)
      (σ:[Δ --> Γ]) (a:Elt (A ⋅ σ)) : 
  LamT B °°° σ {{a}} ~1 B ⋅ (SubExt σ a).
  exists (fun t => identity _).
  econstructor. intros; mysimpl. eapply composition. apply equiv_id_L.
  apply inverse. eapply composition. apply equiv_id_R.
  unfold _map; simpl. unfold SubstT_1_obligation_1,groupoid.arrow_comp_obligation_1.
  unfold _map; simpl. unfold SubExt_1_obligation_1, Curry1_obligation_1.
  unfold groupoid.arrow_comp_obligation_1.
  apply inverse. eapply composition. eapply inverse. apply (map_comp B).
  apply (map2 B).   Transparent _Type _Type_comp.
  simpl; red; simpl.
  exists (id_R _ _ _). unfold eq_rect_eq, eq_rect_comp. mysimpl. simpl_id_bi.
  eapply composition. apply comp. apply map2_id_R. apply identity. simpl.
  simpl_id.
  unfold equiv_adjoint. simpl. apply inverse.
  eapply composition. apply assoc. eapply composition.
  apply comp. apply comp. apply identity. apply _map_comp. apply identity.
  eapply composition. eapply inverse. apply assoc. apply inverse.
  eapply composition. eapply inverse. apply assoc.
  apply comp; [apply identity | idtac]. apply inverse.
  eapply composition. eapply inverse. apply assoc.
  apply comp; [apply identity | idtac].
  eapply composition. apply comp.
  eapply composition. apply _map_comp. apply comp.  apply map_inv. apply identity.
  apply identity.
  eapply composition. eapply inverse. apply assoc.
  eapply composition. eapply comp. apply identity.
  apply (α_map (section (map A (map σ e)))).
  eapply composition. eapply assoc. eapply composition; try apply id_R.
  apply comp; [idtac | apply identity].
  eapply right_simplify'.   eapply composition. eapply assoc.
  eapply composition. apply comp. apply inv_L. apply identity. simpl_id_bi.
  apply inverse. apply (triangle (map A (map σ e))).
Defined.

(* begin hide *)

Instance Var_1 {Γ:Context} (A:Typ Γ) :  
  WeakDependentFunctor ⇑ A (λ t : sigma (λ t : [Γ], [A @ t]), Π2 t).
Next Obligation. intros. apply (Π2 e). Defined.
Next Obligation. intros. unfold Var_1_obligation_1. simpl. 
                 apply comp; try apply identity. unfold eq_rect_comp.
                 eapply composition. eapply inverse. apply id_R.
                 apply comp; try apply identity. eapply inverse. 
                 unfold eq_rect. simpl. unfold groupoid.arrow_comp_obligation_1.
                 simpl. 
                 assert (map2 A (comp _ _ _ _ _ _ _ (identity [e]) (identity [e'])) ~ identity (map A ([e'] °[e]))). 
                 trunc_eq.
                 apply X.
Defined.
Next Obligation. intros. apply (Π2 H). Defined.

(* end hide *)

(**

  ** Interpretation of typing judgments 
  %\label{sec:interp}%

  The judgdment of %\CCu\xspace% of Figure %\ref{fig:coc}% are interpreted in the 
  weak groupoid model as below.

  %\paragraph{\textsc{Var}.}% 

  The rule %\textsc{Var}% is given by the second projection plus a proof
  that the projection is dependently functorial. Note the explicit
  weakening of [A] in the returned type. This is because we need to
  make explicit that the context used to type [A] is extended with an
  element of type [A]. The rule of Figure %\ref{fig:coc}% is more general 
  as it performs an implicit weakening. We do not interpret this part of 
  the rule as weakening is explicit in our model. 

*)


Definition Var {Γ} (A:Typ Γ) : Elt ⇑A := (λ t, Π2 t; _). 
Next Obligation. intros. exact (Var_1 A). Defined.

(* begin hide *)

Instance Prod_1 {Γ} (A:Typ Γ) (F:TypFam A) :
  WeakFunctor (λ s : [Γ], _Prod ([F] s) : [_Type]).
Next Obligation. intros. apply (Prod_eqT F X). Defined.
Next Obligation. intros. simpl. red. simpl. exists (inverse (Prod_eq_comp F e e')).
                 apply AllEquivEq.
Defined.
Next Obligation. intros. simpl. red. simpl. exists (Prod_eq_map F e e' X).
                 apply AllEquivEq.
Defined.
(* end hide *)

(**

  %\paragraph{\textsc{Prod}.}%

  The rule %\textsc{Prod}% is interpreted using 
  the dependent functor space, plus a proof that equivalent 
  contexts give rise to isomorphic dependent functor spaces.
  Note that the rule is defined on type families and not on dependent 
  type because here we need a fibration point of view.

*)

Definition Prod {Γ} (A:Typ Γ) (F:TypFam A) : Typ Γ :=
  (λ s, _Prod (F @ s); _).

(* begin hide *)

Instance App_1 {Γ} {A:Typ Γ} {F:TypFam A} (c:Elt (Prod F)) (a:Elt A) :
  WeakDependentFunctor (F {{a}}) (λ s : [Γ], [[c] s] ([a] s)).

Next Obligation. intros. eapply composition; try apply (Dmap (c @ y) (Dmap a e)).
                 unfold eq_rect.
                 eapply composition; try eapply
                   (map [map ([F] y) (Dmap a e)] (Dmap c e @ ([map A e] @ (a @ x)))).
                 unfold eq_rect. simpl. (* unfold _map at 2; simpl. *)
                 unfold Prod_eq_1. simpl. unfold id.
                 eapply composition; try apply (α_map (Dmap F e) (Dmap a e)).
                 simpl. apply _map. (* unfold _map at 2; simpl. *)
                 unfold equiv_adjoint.
                 eapply composition.
                 apply (map_comp (F @ x) _ (map (adjoint (map A e)) (Dmap a e))). simpl.
                 apply _map. apply (Dmap (c @ x)).
Defined.
Next Obligation. admit. Defined.
Next Obligation. admit. Defined.
 
(* end hide *)

(**

  %\paragraph{\textsc{App}.}%

  The rule %\textsc{App}% is interpreted using an up-to context application 
  and a proof of dependent functoriality. We abusively note [M @@ N] the application 
  of [App].

*)

Definition App {Γ} {A:Typ Γ} {F:TypFam A}
  (c:Elt (Prod F)) (a:Elt A) : Elt (F {{a}}) :=
  (λ s, (c @ s) @ (a @ s); _).
Next Obligation. intros. exact (App_1 c a). Defined.

(* begin hide *)

Notation "M '@@' N" := (App M N) (at level 50).

Instance Lam_1 {Γ} {A:Typ Γ} {F:TypDep A}
  (b:Elt F) (γ:[Γ]) :
  WeakDependentFunctor ([LamT F] γ) (fun t => b @ (γ ; t)).
Next Obligation. intros. apply (Dmap b (sum_id_left e)).
Defined.
Next Obligation. intros. eapply composition. eapply (Dmap2 b (inverse (sum_id_left_comp _ _ _ _ _ _))).
                 eapply composition. apply comp. apply identity.
                 apply (Dmap_comp b). eapply composition. apply assoc. apply identity.
Defined.
Next Obligation. intros. eapply (Dmap2 b (sum_id_left_map _ _ _ _ _ H)).
Defined.

Definition Lam_partial {Γ} {A:Typ Γ} {F:TypDep A}
  (b:Elt F) (γ:[Γ]) : [Prod (LamT F) @ γ] :=
 (λ t, b @ (γ ; t) ; _). 
Next Obligation. intros. exact (Lam_1 _ _). Defined.

Instance Lam_2 {Γ} {A:Typ Γ} {B:TypDep A} (b:Elt B) :
 WeakDependentFunctor (Prod (LamT B)) (Lam_partial b).
Next Obligation. intros. simpl. red; simpl. unfold Prod_eq_1, id. simpl. unfold id.
                 exists (fun t => Dmap b (sum_id_right e t)). 
                 econstructor. intros; simpl. 
                 admit.
Defined.
Next Obligation. intros. simpl. red. intro; simpl. admit. Defined.
Next Obligation. intros. simpl. red. intro; simpl. admit. Defined.

(* end hide *)

(**

  %\paragraph{\lrule{Lam}.}%

  Term-level $\lambda$-abstraction is defined with the same
  computational meaning as type-level $\lambda$-abstraction, but it
  differs on the proof of dependent functoriality. Note that we use
  [LamT] in the definition because we need both the fibration (for
  [Prod]) and the morphism (for [Elt B]) point of view.
  
*)

Definition Lam {Γ} {A:Typ Γ} {B:TypDep A} (b:Elt B) :
  Elt (Prod (LamT B)) := (λ γ, (λ t, b @ (γ ; t) ; _); _).
Next Obligation. intros. exact (Lam_1 _ _). Defined.
Next Obligation. intros. (* exact (Lam_2 b). *) admit. Defined.


(**

  %\paragraph{\lrule{Conv}.}%

  It is not possible to prove in %\Coq% that the conversion rule is
  preserved because the application of this rule is implicit and
  can not reified. Nevertheless, to witness this preservation, 
  we show that beta conversion is valid as a Leibniz 
  equality on the first projection. As conversion is only done on 
  types and interpretation of types is always projected, this is 
  enough to guarantee that the conversion rule is admissible.

*)

Lemma Beta {Γ} {A:Typ Γ} {F:TypDep A} (b:Elt F) (a:Elt A) : 
  [Lam b @@ a] = [b °° SubExtId a].
reflexivity.
Defined.
(**
 %\noindent% where [SubExtId] is a specialization of [SubExt] with 
  the identity substitution.
*)

(* begin hide *)

Notation "e 'with' t" := (prod_eq t @ e) (at level 50).

(* end hide *)

(** 
 ** Sort

  Sorts can be seen as non-dependent types. They are thus interpreted using 
  the [non_dep_type] function that constructs a constant dependent type from a type. 

*)

Definition non_dep_type {Γ} T : Typ Γ := (λ γ, T; _).

(** 

  We can define the interpretation of [Type] as [type := non_dep_type _Type]. 
  Note that again, the definition of [type] 
  requires universe polymorphism to be accepted.

  To interpret [Prop], we first need to introduce [_Prop], the equivalent of [_Type] 
  at the level of propositions. 

   Equality on proofs is irrelevant, i.e., the set of (iso-)Homs between
   any two proofs of the same proposition is a singleton.
   We define an instance [IrrRelWeakGroupoid] that constructs a weak
    groupoid from an equivalence by assuming that the second equality
    is irrelevant. We use this instance to define weak groupoids
    degenerated at level 2, as for instance for [Prop].

    As we want a coercion from [_Prop] to [_Type], they have to share the 
   same structure. So an inhabitant of [_Prop] needs to be propositions 
   with a structure of weak groupoid. But as equality on propositions is irrelevant,
   the weak groupoid structure is trivial and can be implicit.

*)

Definition Propositions := { P : Prop & unit }.


(** Equality between propositions of type [Propositions] is given by
logical equivalence on the underlying propositions, i.e., propositional
extensionality. This is a degenerate case of univalence, where the
proofs that the two maps form an isomorphism is trivial due to
the above definition of equality of witnesses: they are all equal.  *)
  
(* begin hide *)
Program Instance Prop_id : Identity (λ P Q : Propositions, [P] <-> [Q]).
Next Obligation. firstorder. Defined.

Program Instance Prop_inv : Inverse (λ P Q : Propositions, [P] <-> [Q]).
Next Obligation. firstorder. Defined.

Program Instance Prop_comp : Composition (λ P Q : Propositions, [P] <-> [Q]).
Next Obligation. firstorder. Defined.
(* end hide *)

Definition _Prop : WeakGroupoidType := 
  (Propositions; IrrRelWeakGroupoid {| eq1 := (λ P Q, [P] <-> [Q]) |}).

(** %\noindent% As for [Type], we interpret [Prop] as [Ω := non_dep_type _Prop].

*)

(* begin hide *)

Definition eq_ind (A : [_Type]) {x y : [A]} (F: [A --> _Prop])
  (e : x ~1 y) : [F @ x] -> [F @ y].
exact (let (l,_) := (map F e) in l). Defined.

Definition Ω {Γ} : Typ Γ := non_dep_type _Prop.

Definition type {Γ} : Typ Γ := non_dep_type _Type.

Definition PropToTypeT (P:[_Prop]) : [_Type] := 
  ([P]; IrrRelWeakGroupoid {| eq1 := Hom_irr [P] |}).

Definition PropToType_eq' (P Q:[_Prop]) (e : P ~1 Q) : 
  PropToTypeT P ---> PropToTypeT Q.
  destruct e. exists H. econstructor. 
  firstorder. firstorder. Grab Existential Variables. econstructor; firstorder. 
Defined.

Definition PropToType_comp (P Q R:[_Prop]) (e : P ~1 Q) (e' : Q ~1 R) : 
  PropToType_eq' (e' ° e) ~1 PropToType_eq' e' ° PropToType_eq' e.
  exists (fun _ => tt). econstructor. firstorder. Defined.

Definition PropToType_eq_eq (P Q:[_Prop]) (e e': P ~1 Q) (H : e ~2 e') : 
  PropToType_eq' e ~1 PropToType_eq' e'.
  exists (fun _ => tt). econstructor. firstorder. Defined.

Instance PropToType_iso (P Q:[_Prop]) (e : P ~1 Q) : 
  Iso_struct (PropToType_eq' e).
Next Obligation. intros. exact (PropToType_eq' (inverse e)). Defined.
Next Obligation. intros. exists (fun t => tt). econstructor. firstorder. Defined.
Next Obligation. intros. exists (fun t => tt). econstructor. firstorder. Defined.

Instance PropToType_equiv (P Q:[_Prop]) (e : P ~1 Q) : 
  Equiv_struct (PropToType_eq' e).
Next Obligation. firstorder. Defined.

Definition PropToType_eq (P Q:[_Prop]) (e : P ~1 Q) : 
  PropToTypeT P ~1 PropToTypeT Q := (PropToType_eq' e; _). 
Next Obligation. intros. exact (PropToType_equiv _ _ _). Defined.

Definition Props (Γ:Context) := [Γ --> _Prop].

Instance PropsToTyp_1 (Γ:Context) (A:Props Γ) : 
WeakFunctor (λ s : [Γ], PropToTypeT ([A] s)).
Next Obligation. intros. apply PropToType_eq. exact (map A X). Defined.
Next Obligation. intros. simpl. red. simpl. 
                 exists (PropToType_comp _ _  ° 
                        PropToType_eq_eq (map_comp A e e')).
                 econstructor; firstorder. Defined.
Next Obligation. intros. simpl. red; simpl. exists (PropToType_eq_eq (map2 A X)).
                 econstructor; firstorder. Defined.                 

Definition PropsToTyp (Γ:Context) (A:Props Γ) : Typ Γ :=
  (λ s, PropToTypeT (A @ s); _).

Definition EquProp_ (P Q : [_Prop]) : [_Prop]. 
exists ([P] <-> [Q]). econstructor. Defined.

Definition EquPropT {Γ: Context} (P Q :Props Γ) : Props Γ. 
exists (fun s => EquProp_ (P @ s) (Q @ s)). 
econstructor. firstorder. firstorder. Grab Existential Variables. firstorder.
apply (map Q X). apply H.
apply (map P (inverse X)). apply H1. 
apply (map P X). apply H0.
apply (map Q (inverse X)). apply H1. 
apply (map Q (inverse X)). apply H.
apply (map P X). apply H1. 
apply (map P (inverse X)). apply H0.
apply (map Q X). apply H1. Defined.

Notation  "P '<-T->' Q" := (EquPropT P Q) (at level 50). 

Program Instance TypeToType_1 {Γ:Context} (A : Elt (Γ:=Γ) type) : 
  WeakFunctor ([A] : [Γ] -> [_Type]).
Next Obligation. intros. apply (Dmap A X). Defined. 
Next Obligation. intros. eapply composition. apply (Dmap_comp A e e'). 
                 eapply composition. apply equiv_comp.
                 apply (@inv_id _Type). apply identity.
                 apply equiv_id_R. Defined. 
Next Obligation. intros. eapply composition. apply (Dmap2 A X). 
                 apply equiv_id_R. Defined. 

Definition TypeToType {Γ:Context} (A : Elt (Γ:=Γ) type) : Typ Γ := ([A]; _).

Definition PropToProp {Γ:Context} (A : Elt (Γ:=Γ) Ω) : Props Γ := ([A]; _).
Next Obligation. econstructor. firstorder. firstorder. Grab Existential Variables.
                 econstructor; apply (Dmap A X). Defined.

Definition PropToType {Γ:Context} (A : Elt (Γ:=Γ) Ω) : Typ Γ := 
  PropsToTyp (PropToProp A).

Definition PropToProp2 {Γ:Context} (A : Props Γ) : Elt (Γ:=Γ) Ω := ([A]; _).
Next Obligation. econstructor. firstorder. firstorder.
                 Grab Existential Variables. intros. apply (map A e).
Defined.

Definition EquProp {Γ: Context} (P Q : Elt (Γ:=Γ) Ω) : Elt (Γ:=Γ)  Ω :=
  PropToProp2 (PropToProp P <-T-> PropToProp Q).

Notation  "P '<-->' Q" := (EquProp P Q) (at level 50). 

Coercion PropToType : Elt >-> Typ.

(* end hide *)

(** 

  ** Extensional principles
  %\label{sec:extprinc}%
 
  One of the main interest of the groupoid interpretation is that it
  validates various extensional principles.

 Using a coercion [PropToType : Elt Ω -> Typ Γ] that lifts
 propositions to types and lifting the logical equivalence to [Ω], 
 propositional extensionality is admissible in our model.

*)

Definition prop_extensionality Γ (P Q : Elt (Γ:=Γ) Ω) 
  (π : Elt (PropToType (P <--> Q))) : P ~1 Q.
Proof. exists [π]. econstructor. firstorder. Defined.

(* begin hide *)

Definition proof_irrelevant {Γ: Context} (P : Elt (Γ:=Γ) Ω) 
(p q :  Elt (PropToType P)) : p ~1 q.
Proof.
  econstructor. econstructor. simpl. intros. firstorder. 
  Grab Existential Variables. simpl. firstorder. 
Qed.

Lemma eq_Prod_ctxt {T Γ} (A:Typ Γ) (F:TypFam A) (f: [T --> Γ]) :
  (* Prod F ⋅ f ~1 Prod (F °°° f). *)
  (@eq1 (nat_transHom _ _)) (Prod F ⋅ f) (Prod (F °°° f)).
  exists (fun t => identity (_Prod ([F] ([f] t)))). econstructor. intros. 
  mysimpl. eapply composition. apply equiv_id_L. apply inverse.
  eapply composition. apply equiv_id_R.
  unfold _map. simpl. unfold groupoid.arrow_comp_obligation_1; simpl.
  unfold Prod_1_obligation_1.
  red. simpl. admit.
Defined.

Notation "↑ t" := (t °° SubWeak with eq_Prod_ctxt _ _) (at level 9, t at level 9).
 
Definition Dmap_id_adjoint {Γ} {A:Typ Γ} (F:TypFam A) {γ : [Γ]}
  {x y : [A @ γ]} (e : x ~1 y) : [Dmap F (identity γ)] y °
          (map ([F] γ) (equiv_adjoint (Var A) (sum_id_left e)))
 ~ map ([F] γ) e.
admit.
Defined.

Definition FunExt_1_aux (Γ: Context) (A : Typ Γ)
        (F : TypDep A) (M : Elt (Prod (LamT F))) (γ : [Γ])
        (t t' : [A @ γ]) (e : t ~1 t') :
  Dmap (M @ γ) e ° ([Dmap_id_adjoint (LamT F) e] @ ([[M] γ] t)) ~
App_1_obligation_1 
    (F := substF (LamT F) SubWeak)
    (λ a : [_Sum A], M @ [a];
     prod_eq1 (_Sum A) (Prod (LamT F) ⋅ SubWeak) (Prod (LamT F °°° SubWeak)) (eq_Prod_ctxt (LamT F) SubWeak) (M °° SubWeak)) (Var A)
    (γ; t) (γ; t') (sum_id_left e). 
admit. Defined.


Definition FunExt_1 (Γ: Context) (A : Typ Γ) 
        (F : TypDep A) (M N : Elt (Prod (LamT F))) 
        (α : ↑M @@ Var A ~1 ↑N @@ Var A) : 
          ∀ γ : [Γ], M @ γ ~1 N @ γ. 
destruct α as [α [H]]. simpl. unfold id in H.
intro. simpl in α. 
exists (fun t => α (γ ; t)). 
econstructor. intros; simpl in *.
eapply right_simplify'. eapply composition. apply assoc.
eapply composition. apply comp.
set (HFun := FunExt_1_aux M γ t t' e).
exact (FunExt_1_aux M γ t t' e). apply identity.
eapply composition. apply (H _ _ (sum_id_left e)).
unfold eq_rect_map. eapply composition. apply comp. apply identity.
eapply inverse. apply FunExt_1_aux.
unfold _map; simpl. eapply composition. apply assoc. apply inverse.
eapply composition. apply assoc. apply comp; [idtac | apply identity].
apply inverse. apply (α_map [Dmap_id_adjoint (LamT F) e]).
Defined.

(* end hide *)

(** As the whole interpretation is functorial with respect to a context,
  the naturality condition required on equality between dependent
  functors can be deduced from the existence of a transformation. 
  This allows to state dependent functional extensionality. *)


Definition FunExt (Γ: Context) (A : Typ Γ) 
  (F : TypDep A) (M N : Elt (Prod (LamT F))) 
  (α : ↑M @@ (Var A) ~1 ↑N @@ (Var A)) : M ~1 N.
Proof.
exists (FunExt_1 α). 
econstructor. intros; simpl. red. intros. simpl.
assert ([Dmap (LamT F) [sum_id_right e t0]] t0 °
        (_map (equiv_adjoint (Var A) (sum_id_right e t0)))
                ~ [Dmap (LamT F) e] t0).
admit.
assert (foo : forall M: Elt (Prod (LamT F)), 
                [Dmap M e] t0 ° ([X] @ ([[M] t] ([adjoint (map A e)] t0))) ~

                App_1_obligation_1 (F := substF (LamT F) SubWeak)
          (λ a : [_Sum A], [M] [a];
          prod_eq1 (_Sum A) (Prod (LamT F) ⋅ SubWeak) (Prod (LamT F °°° SubWeak))
            (eq_Prod_ctxt (LamT F) SubWeak) (M °° SubWeak)) (Var A)
          (t; [adjoint (map A e)] t0) (t'; t0) (sum_id_right e t0) 
       ).
mysimpl.
admit.
eapply right_simplify'. eapply composition. apply assoc.
eapply composition. apply comp. exact (foo M). apply identity.
destruct α as [α [H]]. eapply composition. apply (H _ _ (sum_id_right e t0)).
unfold eq_rect_map. eapply composition;[apply comp;[apply identity|]|].
eapply inverse. apply foo. mysimpl. clear foo H. eapply composition. apply assoc. 
apply inverse. eapply composition. apply assoc. apply comp; [idtac | apply identity].
apply inverse. apply (α_map [X] (α (t; [adjoint (map A e)] t0))).
Defined.

(** 
  %\noindent% where [↑M] is the weakening for terms. This rule corresponds 
  to the introduction of equality on dependent functions in %\cite{DBLP:conf/popl/LicataH12}%.
*)

(* begin hide *)


Definition FunExt_Elim (Γ: Context) (A : Typ Γ) 
        (F : TypDep A) (M N : Elt (Prod (LamT F))) (a : Elt A) (α : M ~1 N)
        : M @@ a ~1 N @@ a.
exists (fun γ => ((α @ γ) @ (a @ γ))). econstructor. intros; simpl. 
admit. Defined.

Definition Conversion_Eq (Γ: Context) (A B: Typ Γ) 
        (t : Elt A) (e : A = B) : Elt B.
Proof. destruct e. exact t. Defined.

(* end hide *)

(** We can finally interpret a homotopical version of rewriting at the
  level of types. *)

Definition Heq_rect Γ (A B: Typ Γ) (e : A ~1 B) : 
  Elt A -> Elt B.
Proof. exact (fun t => prod_eq e @ t). Defined.
