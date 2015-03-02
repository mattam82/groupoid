
(* Definition Conversion_Eq (Γ: Context) (A B: Typ Γ)  *)
(*         (t : Elt A) (e : A = B) : Elt B. *)
(* Proof. destruct e. exact t. Defined. *)

(* (** We can finally interpret a homotopical version of rewriting at the *)
(*   level of types. *) *)

(* Definition Heq_rect Γ (A B: Typ Γ) (e : A ~1 B) :  *)
(*   Elt A -> Elt B. *)
(* Proof. exact (fun t => prod_eq e @ t). Defined. *)

(* end hide *)


(*
(* begin hide *)

Program Instance set_fun_1 (Γ: Context) (A B : Typ Γ) : Functor (T := [[Γ]]) (U:=Type0) (fun γ => A @ γ -|-> B @ γ).
Next Obligation. intros. simpl. apply (fun_eqT (map A X) (map B X)). Defined.
Next Obligation. intros. unfold set_fun_1_obligation_1. 
                 exists (fun_eq_id2 ([[[A]]]) ([[[B]]]) x). 
                 red. red. intro. intro. trunc1_eq. Defined.

Next Obligation. intros. unfold set_fun_1_obligation_1. 
                 exists (fun_eq_eq' _ _ _ _ ° fun_eq_eq (map_comp A e e') (map_comp B e e')).
                 red. red. intro. intro. trunc1_eq. Defined.
Next Obligation. intros. unfold set_fun_1_obligation_1. 
                 exists (fun_eq_eq (map2 A X) (map2 B X)).
                 intros f t. 
                 trunc1_eq.
Defined.

Definition set_fun (Γ: Context) (A B : Typ Γ) : Typ Γ :=
  (fun γ : [Γ] => A @ γ -|-> B @ γ; set_fun_1 Γ A B).

(* Definition set_fun (Γ: Context) (A B : Typ Γ) : Typ Γ := Prod (cst_fibration A B).  *)

Infix "---->" := set_fun (at level 55). 

Program Instance AppF_1 {Γ} {A B:Typ Γ} (f:Elt (A ----> B)) (a:Elt A) :
  DependentFunctor ([[[B]]]) (λ s : [Γ], (f @ s) @ (a @ s)).
Next Obligation. eapply composition.  simpl in *.
                 assert (f @ x @ (a @ x) ~1 f @ x @ (adjoint (map A e) @ (a @ y))).
                 apply (map (f @ x)). apply (Equiv_injective (map A e)). 
                 eapply composition. apply (Dmap a). apply inverse.
                 apply (section (map A e)). 
                 apply (map [map B e] X).
                 apply (Dmap f e @ (a @ y)).
Defined.
Next Obligation. trunc1_eq. Defined.
Next Obligation. trunc1_eq. Defined.
Next Obligation. trunc1_eq. Defined.

Definition AppF {Γ} {A B:Typ Γ} (f:Elt (A ----> B)) (a:Elt A)
: Elt B := (λ s, (f @ s) @ (a @ s); AppF_1 _ _).

Program Instance ndep_ {Γ} (T:Context) : Functor (T := [[Γ]]) (U:=Type0) (λ γ, T).
Next Obligation. apply identity. Defined.
Next Obligation. apply identity. Defined.
Next Obligation. apply equiv_eq_nat_trans. simpl. exists (fun _ => identity _). 
                 red. intros. simpl. simpl_id_bi.
Defined.
Next Obligation. apply identity. Defined.
  
Definition ndep {Γ} (T:Context) : Typ Γ := (λ γ, T; ndep_ _).

Definition eq_fun_ctxt {T Γ} (A B: Typ Γ) (f: [T -|-> Γ]) :
  nat_trans ((A ----> B) ⋅⋅ f)  (A ⋅⋅ f  ----> B ⋅⋅ f).
  red; simpl. exists (fun t => identity _). red. intros.
  eapply composition. apply equiv_id_L.
  apply inverse. apply equiv_id_R. 
Defined.

Notation "e 'with' t" := (prod_eq' t @ e) (at level 50).

Notation "↑ t" := (t °° Sub with eq_fun_ctxt _ _ _) (at level 9, t at level 9). 

Notation "'Forall' X" := (Prod (LamT X)) (at level 55).
 
Program Instance UId__ {Γ} (A B: Typ Γ) (γ : [Γ]) : Setoid (Equiv' (A @ γ) (B @ γ)).
Next Obligation. econstructor. intros. 
                 apply (@contr_equiv _ _ _ (isequiv_inverse _ _ _ (isequiv_apD10 _ E E'))).
                 apply contr_forall. intros z.
                 apply (@is_Trunc_2 _ _ _ _ _ _ (E z) (E' z)).
Defined.
Next Obligation.
  apply (@contr_equiv _ _ _ (path_sigma_equiv e e')).
  apply (@contr_sigma _ (fun p => p # e.2 = e'.2)).
  apply (@contr_equiv _ _ _ (path_sigma_equiv e.1 e'.1)).
  apply (@contr_sigma _ (fun p => p # e.1.2 = e'.1.2)).
  apply (@contr_equiv _ _ _ (isequiv_inverse _ _ _ (isequiv_apD10 _ [e.1] [e'.1]))).
  apply contr_forall. intros z.
  apply (@is_Trunc_1 _ _ _ _ (e.1 @ z) (e'.1 @ z)).
  intros. destruct e, e'. destruct proj1, proj0. simpl in *. destruct a. simpl. 
  apply (@contr_equiv _ _ _ (isequiv_inverse _ _ _ (isequiv_apD10 _ _ _))).
  apply contr_forall. intros t. 
  apply (@contr_equiv _ _ _ (isequiv_inverse _ _ _ (isequiv_apD10 _ _ _))).
  apply contr_forall. intros t'. 
  apply (@contr_equiv _ _ _ (isequiv_inverse _ _ _ (isequiv_apD10 _ _ _))).
  apply contr_forall. intros e. 
  apply (@is_Trunc_2 _ _ _ _ _ _ _ _).
  intros. destruct e, e'. destruct proj1, proj0. simpl in *. destruct a. simpl. 
  apply (@contr_equiv _ _ _ (isequiv_inverse _ _ _ (isequiv_apD10 _ _ _))).
  apply contr_forall. intros t. 
  apply (@is_Trunc_2 _ _ _ _ _ _ _ _).
Defined.

Definition UId_ {Γ} (A B: Typ Γ) (γ : [Γ]) : [Type0] :=
  (Equiv' (A @ γ) (B @ γ);  UId__ _ _ _).

Program Instance UId_1_fun_ {Γ} (A B: Typ Γ) (x y : [Γ]) (e: x ~1 y): 
  Functor (T:=[[ UId_ A B x]]) (U:=[[UId_ A B y]]) (λ X, (map B e ° X) ° (map A e) ^-1).
Next Obligation. apply equiv_eq_nat_trans. apply nat_comp'. apply identity.
                 apply nat_comp'. apply [X]. apply identity. Defined.
Next Obligation. simpl. red. simpl. intro. simpl. simpl_id_bi. Defined.
Next Obligation. simpl. red. simpl. intro. simpl. simpl_id_bi. 
                 apply inverse. apply (map_comp [map B e]). Defined.
Next Obligation. simpl. red. simpl. intro. simpl. simpl_id_bi. 
                 apply (map2 [map B e]). apply (X^-1 (adjoint (map A e) @ t)).
Defined.

Definition UId_1_fun {Γ} (A B: Typ Γ) (x y : [Γ]) (e: x ~1 y): UId_ A B x -S-> UId_ A B y :=
  (λ X, (map B e ° X) ° (map A e) ^-1; UId_1_fun_ A B x y e).

Program Instance UId_1_equiv_struct {Γ} (A B: Typ Γ) (x y : [Γ]) (e: x ~1 y): Iso_struct (UId_1_fun A B x y e).
Next Obligation. exact (UId_1_fun A B y x e^-1). Defined.
Next Obligation. simpl. red. 
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. apply equiv_eq_nat_trans. simpl. red. 
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. simpl.  
                 eapply composition. eapply (map [map B e]). apply (map_inv B).
                 eapply composition. apply (section (map B e)).
                 apply (map [t]). eapply composition. 
                 assert (adjoint (map A e ^-1) ~ [map A e]).
                 eapply composition. eapply Equiv_adjoint.
                 apply (map_inv A). apply (inv_inv _ _ _ (map A e)).
                 apply (X @ (adjoint (map A e) @ t0)). apply (section (map A e)).
                 exists X. red. intros. trunc1_eq.
                 exists X. red. intros. simpl. red. simpl. intro. simpl. trunc1_eq.
Defined.
Next Obligation. eapply composition. Focus 2. 
                 apply (UId_1_equiv_struct_obligation_2 A B y x e^-1).
                 apply nat_comp'. simpl. red. 
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. apply equiv_eq_nat_trans. simpl. red. 
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. simpl.  
                 assert (forall B: Typ Γ, map B e ~ map B (e ^-1) ^-1).
                 clear; intro. apply (map2 B). apply inverse. apply inv_inv.
                 eapply composition. apply X. apply (map [map B (e ^-1) ^-1]).
                 apply (map [t]). apply Equiv_adjoint. apply X.
                 exists X. red. intros. trunc1_eq.
                 exists X. red. intros. simpl. red. simpl. intro. simpl. trunc1_eq.
                 apply identity.
Defined.

Definition UId_1_equiv {Γ} (A B: Typ Γ) (x y : [Γ]) (e: x ~1 y): Equiv' (UId_ A B x) (UId_ A B y)
  := IsoToEquiv (_; UId_1_equiv_struct A B x y e).

Program Instance UId_1 {Γ} (A B: Typ Γ) : Functor (T := [[Γ]]) (U := Type0) (UId_ A B) 
  := {| _map := UId_1_equiv A B |}.
Next Obligation. apply equiv_eq_nat_trans.  
                 red. simpl. red.  
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. simpl. apply equiv_eq_nat_trans. red. red. 
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro.  simpl. eapply composition. apply (map_id B).
                 apply (map [t]). eapply composition. eapply Equiv_adjoint. 
                 apply (map_id A). apply identity. 
                 exists X. red. intros. trunc1_eq.
                 exists X. red. intros. simpl. red. simpl. intro. simpl. trunc1_eq.
Defined. 
Next Obligation. apply equiv_eq_nat_trans.  
                 red. simpl. red.  
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. simpl. apply equiv_eq_nat_trans. red. red. 
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro.  simpl. eapply composition. apply (map_comp B). simpl.
                 apply (map [map B e']). apply (map [map B e]). apply (map [t]).
                 eapply composition. eapply Equiv_adjoint. apply (map_comp A).
                 apply identity.
                 exists X. red. intros. trunc1_eq.
                 exists X. red. intros. simpl. red. simpl. intro. simpl. trunc1_eq.
Defined. 
Next Obligation. apply equiv_eq_nat_trans.  
                 red. simpl. red.  
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. simpl. apply equiv_eq_nat_trans. red. red. 
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. simpl. eapply composition. apply (map2 B X).
                 apply (map [map B e']). apply (map [t]). apply Equiv_adjoint. 
                 apply (map2 A X).
                 exists X0. red. intros. trunc1_eq.
                 exists X0. red. intros. simpl. red. simpl. intro. simpl. trunc1_eq.
Defined. 

Notation "P '@@@' A" := (AppF ↑P A) (at level 50).

Infix "~11" := (Equiv') (at level 50).

(* end hide *)
(** 
  ** Univalence
  %\label{sec:universe}% 
  To interpret the universe $\Univ$, we need to define its syntax and interpretation of syntax as setoids altogether. That is, $\Univ$ requires inductive-recursive definitions to be interpreted.
  As such definition are not available in %\Coq%, we cannot completely interpret $\Univ$%\footnote{The folklore coding trick to encode inductive-recursive definition using an indexed family as done in~\cite{altenkirch-mcbride-wierstra:ott-now} does not work here because it transforms an inductive-recursive Agda Set into a larger universe which is no longer a setoid.}%. Nevertheless, we present a way to interpret the identity type on $\Univ$ and Rule %\textsc{Id-Equiv-Intro}% which corresponds to the univalence axiom for $\Univ$.

   We interpret the identity type on $\Univ$ in the same way as [Id], except that it 
relates two dependent types [A] and [B] instead of terms of a dependent type.
*)

Definition UId {Γ} (A B: Typ Γ) : Typ Γ := (λ γ, (A @ γ ~11 B @ γ ; _); UId_1 A B). 

(**
 To define the notion of isomorphism, we need to define a proper notion of function (noted [A ----> B]) that does not use the restriction of [Prod] to constant type families. This is because the definition of an isomorphism involves two functions that have to be composed in both ways, which lead to universe inconsistency if we use dependent products to encode functions. We define the notion of application (noted [g @@@ f]) for this kind of functions. 
*)

Definition  _iso_section (Γ: Context) (A B : Typ Γ) (f : Elt (A ----> B)) (iso_adjoint : Elt (B ----> A)) := Elt (Prod (LamT (Id (iso_adjoint @@@ (f @@@ Var A)) (Var A)))).

Definition  _iso_retraction (Γ: Context) (A B : Typ Γ) (f : Elt (A ----> B)) (iso_adjoint : Elt (B ----> A)) := Elt (Prod (LamT (Id (f @@@ (iso_adjoint @@@ Var B)) (Var B)))).

Class iso_struct (Γ: Context) (A B : Typ Γ) (f : Elt (A ----> B)) := 
{ iso_adjoint : Elt (B ----> A)  ;
  iso_section : _iso_section f iso_adjoint;
  iso_retract : _iso_retraction f iso_adjoint}.

(* this one does not work ?? *) 

(* Class iso_struct (Γ: Context) (A B : Typ Γ) (f : Elt (A ----> B)) :=  *)
(* { iso_adjoint : Elt (B ----> A)  ; *)
(*   iso_section : Elt (Prod (LamT (Id (iso_adjoint @@@ (f @@@ Var A)) (Var A)))) ; *)
(*   iso_retract : Elt (Prod (LamT (Id (f @@@ (iso_adjoint @@@ Var B)) (Var B))))}. *)

Definition iso (Γ: Context) (A B : Typ Γ) := {f : Elt (A ----> B) & iso_struct f}.
(* begin hide *)

Infix "≡" := UId (at level 55).

Definition Equiv_Intro_ (Γ: Context) (A B : Typ Γ) (e : iso A B) 
           : ∀ γ : [Γ], A @ γ ~11 B @ γ.
Proof.
  intro. apply IsoToEquiv. exists ([e] @ γ). 
  apply (@Build_Iso_struct _ _ _ (@iso_adjoint _ _ _ _ e.2 @ γ)). 
  pose ([@iso_retract _ _ _ _ e.2 @ γ]). 
  simpl in *. exists p. red. intros. simpl.
  trunc1_eq.
  pose ([@iso_section _ _ _ _ e.2 @ γ]). 
  simpl in *. exists p. red. intros. 
  trunc1_eq.
Defined.

Program Instance Equiv_Intro_1 (Γ: Context) (A B : Typ Γ) (e : iso A B) : 
  DependentFunctor ([[[A ≡ B]]]) (Equiv_Intro_ e).
Next Obligation. apply equiv_eq_nat_trans. simpl. red. 
                 match goal with | [ |- sigma (λ α : ?H, _)]
                                   => assert H end.
                 intro. apply (Dmap [e]).
                 exists X. red. intros. trunc1_eq.
Defined.
Next Obligation. intro. simpl. trunc1_eq. Defined.
Next Obligation. intro. simpl. trunc1_eq. Defined.
Next Obligation. intro. simpl. trunc1_eq. Defined.

(* end hide *)

(**
  Then, we can show that this definition of isomorphism corresponds to equivalence of setoids.
  Again, the only extra work is with the management of context lifting. This provides a computational 
  content to the univalence axiom restricted to setoids.
*)

Definition Equiv_Intro (Γ: Context) (A B : Typ Γ) (e : iso A B) : Elt (A ≡ B).
Proof. exact (Equiv_Intro_ e; Equiv_Intro_1 _ _ _ e). Defined.

*)


(* Program Instance Sub_lift_1 {Δ Γ} {A:Typ Γ} (σ: [Δ -|-> Γ]):  *)
(*   Functor (T:=[[_Sum0 (A ⋅⋅ σ)]]) (U:=[[_Sum0 A]])  (λ γt, (σ @ [γt]; eq_section γt)). *)
(* Next Obligation. exists (map σ X.1). apply X. Defined. *)
(* Next Obligation. exists (map_id σ). simpl_id. Defined. *)
(* Next Obligation. exists (map_comp σ _ _). trunc1_eq. Defined. *)
(* Next Obligation. exists (map2 σ X.1). trunc1_eq. Defined. *)


(* Program Definition Sub_lift {Δ Γ} {A:Typ Γ} (σ: [Δ -|-> Γ]): [_Sum0 (A⋅⋅σ) -|-> _Sum0 A]  *)
(*   :=  (λ γt:[ [[_Sum0 (A⋅⋅σ)]] ], (σ @ γt.1 ;γt.2)  ; Sub_lift_1 _). *)


(* Definition Sub_Elt {Δ Γ} {A:Typ Γ} (σ: [Δ -|-> Γ]) (b:Elt A) *)
(*             : Elt (A ⋅⋅ σ). *)
(* Admitted. *)

(* Definition Prod_lamT_eq {Δ Γ} {A:Typ Γ} (σ: [Δ -|-> Γ]) {F:TypDep A}: *)
(*            Prod (LamT (F ⋅⋅ Sub_lift σ)) ~1 Prod (LamT F) ⋅⋅ σ. *)
(*   simpl. red. simpl.  *)
(*   match goal with | [ |- sigma (λ α : ?H, _)] *)
(*                   => assert H end. *)
(*   intro. simpl. red. simpl. apply prod_eqT. simpl. red. simpl. *)
(*   exists (fun _ => identity _). intros  a a' e. simpl_id_bi. *)
(*   apply (map2  *)
(*   trunc1_eq. *)
(*   reflexivity. *)
(*   exists (fun t => identity (Prod0 ([F] ([σ] t)))). *)


(* Definition Beta2 {Δ Γ} {A:Typ Γ} (σ: [Δ -|-> Γ]) {F:TypDep A} (b:Elt F) *)
(*  : [Sub_Elt σ (Lam b)] = [Lam (Sub_Elt (Sub_lift σ) b)]. *)


(* Definition Beta2 {Δ Γ} {A:Typ Γ} (σ: [Δ -|-> Γ]) {F:TypDep A} (b:Elt F)  *)
(*   : [Lam b ⋅σ  ] = [Lam b ⋅ σ  ]. [b °° SubExtId a] := eq_refl _. *)
