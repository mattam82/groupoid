Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Add LoadPath "." as Groupoid.
Require Import Groupoid.HoTT_light.
Require Import Groupoid.groupoid.
Require Import Groupoid.fun_eq.
Require Import Groupoid.groupoid_interpretation_def.
Require Import Groupoid.Equiv_adjoint.
Require Import Groupoid.fun_depfun.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)
Set Program Mode.
Set Primitive Projections.
 
Opaque Equiv_adjoint.
Opaque map_id map_inv.

Obligation Tactic := intros.

Program Instance prod_eq10 (A: [_Type]) (T U : [|A|g --> Type0]) (eqTU : T ~1 U)
        (t : [Prod0 T]) :
        DependentFunctor0 U (λ a : [A], [eqTU @ a] @ (t @ a)).
Next Obligation.
  eapply composition.
  exact ((inverse [α_map eqTU e]) @ (t @ x)).
  exact (map [eqTU @ y] (Dmap t e)).
Defined.
Next Obligation.
  simpl. unfold prod_eq10_obligation_1. trunc1_eq.
Defined.
Next Obligation.
  simpl. unfold prod_eq10_obligation_1. trunc1_eq.
Defined.

Instance prod_eq1 (A: [_Type]) (T U : [|A|g --> Type0]) (eqTU : T ~1 U)
        (t : [Prod0 T]) :
        DependentFunctor ([[[U]]]) (λ a : [A], [eqTU @ a] @ (t @ a))
  := DepFun0DepFun (|A|g) U (_;prod_eq10 A T U eqTU t).

Program Instance prod_eq2 (A: [_Type]) (T U : [|A|g --> Type0]) (eqTU : T ~1 U) :
        Functor (λ (t : [_Prod ([[[T]]])]), (λ a : [A], [eqTU @ a] @ (t @ a)  ; prod_eq1 eqTU t) : [_Prod ([[[U]]])]).
Next Obligation. exists (fun t => map [ [eqTU] t] (X @ t)). red. intros; simpl.
                 unfold groupoid.DepFun0DepFun_obligation_1. simpl.
                 unfold prod_eq10_obligation_1.
                 trunc1_eq.
Defined.
Next Obligation. intro. trunc1_eq. Defined.
Next Obligation. intro. trunc1_eq. Defined.
  
Definition prod_eq (A: [_Type]) (T U : [|A|g --> Type0]) (e:T ~1 U) : [_Prod ([[[T]]]) --> _Prod ([[[U]]])] := (_ ; prod_eq2 A T U e).

Hint Extern 4 (@Composition (@sigma _ GroupoidP) Fun_Type) => exact comp_fun : typeclass_instances.
Hint Extern 4 (@HomT2 (@sigma _ GroupoidP) Fun_Type) => exact nat_transHom' : typeclass_instances.

Definition prod_eq_comp' (A: [_Type]) (T U V: [|A|g --> Type0]) 
        (e:T ~1 U) (e' : U ~1 V) : 
  ∀ t : [_Prod ([[[T]]])], [(prod_eq e') ° (prod_eq e)] t ~1 [prod_eq (e' ° e)] t.
intro; simpl. red; simpl. exists (fun t => identity _). intros. red; intros.
trunc1_eq.
Defined.

Definition prod_eq_comp (A: [_Type]) (T U V: [|A|g --> Type0]) 
           (e:T ~1 U) (e' : U ~1 V) : 
  prod_eq e' ° prod_eq e ~ prod_eq (e' °e) := (prod_eq_comp' e e'; _).
Next Obligation. intros t t' X X'. simpl. simpl_id_bi. Defined.

Definition prod_eq_map' (A: [_Type]) (T U: [|A|g --> Type0]) 
        (e e':T ~1 U) (H : e ~ e') (t:[_Prod ([[[T]]])]) :  
  [prod_eq e] t ~1 [prod_eq e'] t := 
(fun t0 => [H t0] @ (t @ t0); _).
Next Obligation. intros a a' Xa; simpl. trunc1_eq.
Defined.

Definition prod_eq_map (A: [_Type]) (T U: [|A|g --> Type0]) 
        (e:T ~1 U) (e' : T ~1 U) (H : e ~ e') : nat_trans (prod_eq e) (prod_eq e') 
:= (prod_eq_map' H; fun _ _ _ X => α_map [H X] _). 

Hint Extern 4 (@Identity (@sigma _ GroupoidP) _) => exact id_fun : typeclass_instances.

Program Definition prod_eq_id' (A: [_Type]) (T: [|A|g --> Type0])  :
∀ t : [_Prod ([[[T]]])], [prod_eq (identity T)] t ~1 [identity (_Prod ([[[T]]]))] t :=
  fun t => (fun _ => identity _ ;  _). 
Next Obligation. intros a a' Xa; simpl. trunc1_eq.
Defined.

Definition prod_eq_id (A: [_Type]) (T : [|A|g --> Type0]) 
 : prod_eq (identity T) ~ identity _ := (prod_eq_id' (T:=T); _).
Next Obligation. intros t t' e a. simpl. simpl_id_bi. Defined.

Program Instance prod_eq_iso (A: [_Type]) (T U: [|A|g --> Type0]) (e:T ~1 U) : 
  Iso_struct (prod_eq e).
Next Obligation. exact (prod_eq e^-1). Defined.
Next Obligation. (*the proof below should work with polymorphism *)
                 eapply composition. exact (prod_eq_comp (inverse e) e).
                 eapply composition; [idtac | apply prod_eq_id].
                 apply (@prod_eq_map _ _ _ (e ° e ^-1) (identity U)).
                 intro. simpl. apply (equiv_inv_R _ _ (e @ t)).
Defined.
Next Obligation. (*the proof below should work with polymorphism *)
                 eapply composition. exact (prod_eq_comp e (inverse e)).
                 eapply composition; [idtac | apply prod_eq_id].
                 apply (@prod_eq_map _ _ _ (e ^-1 ° e) (identity T)).
                 intro. simpl. apply (equiv_inv_L _ _ (e @ t)).
Defined.

Program Definition prod_eqT (A: [_Type]) (T U: [|A|g --> Type0]) (e:T ~1 U) : 
  _Prod ([[[T]]]) <~> _Prod ([[[U]]]) := IsoToEquiv (prod_eq e; prod_eq_iso _ _ _ e).

(* An other version of prod_eq *)

Program Definition Prod_eq_ {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y) : 
  [F] x ° adjoint (map A e) ~ [F] y 
  := Dmap F e ° inverse (nat_id_L ([F] x ° adjoint (map A e))).

Program Definition Prod_eq_1 {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y)
        (X: Prod_Type ([[[F @ x]]])) (a : [A @ y]) : [(F@ y) @ a] :=
 [Prod_eq_ F e @ a] @ ((X °° adjoint (map A e)) @ a).

Program Instance Prod_eq_2 {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y)
(X: Prod_Type ([[[F @ x]]])) : DependentFunctor ([[[F @ y]]]) (Prod_eq_1 F e X) :=
  @prod_eq1 ([[A @ y]]) _ (F @ y) (Prod_eq_ F e) (X °° adjoint (map A e)).

Program Instance Prod_eq_3 {Γ} (A:Typ Γ) (F:TypFam A) {x y : [Γ]} (e:x~1 y) :
 Functor (λ X : [_Prod ([[[F @ x]]])],
         (λ a, Prod_eq_1 F e X a; Prod_eq_2 A F e X) : [_Prod ([[[F @ y]]])]).
Next Obligation. exists (fun a => map [Prod_eq_ F e @ a] 
                                      (X @ ([adjoint (map A e)] a))).
                 red; intros. trunc1_eq.
Defined.
Next Obligation. intro. intros. simpl. apply (map_comp [Dmap F e @ t]). Defined.
Next Obligation. simpl; red; intros; simpl. apply (map2 [Dmap F e @ t] (X _)). Defined.

Program Definition Prod_eq {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y): 
 _Prod ([[[F @ x]]]) ---> _Prod ([[[F @ y]]]) := (_; Prod_eq_3 A F e).

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
red; intros. trunc1_eq.
Defined.

Program Definition Prod_eq_comp {Γ} (A:Typ Γ) (F:TypFam A) {x y z: [Γ]}
        (e:x~1 y) (e' : y ~1 z): Prod_eq F e' ° Prod_eq F e ~ Prod_eq F (e' °e).
exists (Prod_eq_comp' F e e'). red. intros. simpl. red. intros. trunc1_eq. Defined.

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
Next Obligation. unfold Prod_eq_iso_obligation_1.
                 eapply composition. apply Prod_eq_comp. 
                 eapply composition; [idtac | apply Prod_eq_id]. 
                 apply Prod_eq_map. apply inv_R. 
Defined.
Next Obligation. eapply composition. apply Prod_eq_comp. 
                 eapply composition; [idtac | apply Prod_eq_id]. 
                 apply Prod_eq_map. apply inv_L. 
Defined.

Definition Prod_eqT {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y): 
  _Prod ([[[F @ x]]]) <~> _Prod ([[[F @ y]]]) := IsoToEquiv (Prod_eq F e; Prod_eq_iso _ F e).


Ltac mysimpl := 
  simpl (@proj1); simpl (@proj2).

Ltac trunc_eq' := match goal with
         | [ |- [?e] @ ?t ~ [?e'] @ ?t] =>
          let X := fresh in
          let X':=fresh in 
          set(X:=e) in *; 
          set(X':=e') in *;
          let H := fresh in
           assert (H:=@HoTT_light.center _ (Trunc_2 (T:=Type0) _ _ _ _ X X')) ;
             try ((destruct H; apply identity) 
                    || (simpl in *; destruct H; apply identity))
       end.

Lemma nat_trans_comp (A: [_Type]) (T U : [|A|g --> _Type]) (α : T ~1 U)
  (x y z  : [A]) (e : x ~1 y) (e' : y ~1 z) :
  (identity _ ** map_comp U e e') ° α_map α (e' ° e) ~2
     inverse (assoc'') ° (α_map α e ** identity _ ) ° assoc'' °
     (identity _ ** α_map α e') ° inverse (assoc'') °
     (map_comp T e e' ** identity _).
Proof. admit. Defined.

Lemma nat_trans_id (A: [_Type]) (T U : [|A|g --> _Type]) (α : T ~1 U)
  (x : [A]) :
       (identity _ ** map_id U) ° α_map α (identity _) ~2
       inverse (id_L' _) ° id_R' _ ° (map_id T (x:=x) ** identity _).
Proof. admit. Defined.

Lemma nat_trans2 (A: [_Type]) (T U : [|A|g --> _Type]) (α : T ~1 U)
  (x y : [A]) (e e' : x ~1 y) (H : e ~e') :
  (identity _ ** (map2 U H)) ° (α_map α e) ~ (α_map α e') ° ((map2 T H) ** identity _).
Proof. admit. Defined.

Definition inv_left_right (A:[_Type]) (x y z :[A]) (f : y ~1 z) (g: y ~1 x) (h:x ~1 z) :
  f ~2 h ° g -> f ° inverse g ~2 h.
  intro. eapply (@right_simplify' (|A|g)). 
  eapply composition; try exact X.
  eapply composition. apply assoc. eapply composition.
  apply comp. apply inv_L. apply identity. apply id_R.
Defined.

Definition inv_left_right' (A:[_Type]) (x y z :[A]) (f : y ~1 z) (g: y ~1 x) (h:x ~1 z) :
  f ~2 h ° g  -> inverse h ° f ~2 g.
  intro. eapply (@left_simplify' (|A|g)). 
  eapply composition; try exact X.
  eapply composition. eapply inverse. apply assoc. eapply composition.
  apply comp. apply identity. apply inv_R. apply id_L.
Defined.

Instance prod_eq1' (A:[_Type]) (T U : [|A|g --> _Type]) (eqTU : T ~1 U)
        (t : [_Prod T]) :
        DependentFunctor U (λ a : [A], [eqTU @ a] @ (t @ a)).
Next Obligation.
  eapply composition.
  exact ((inverse [α_map eqTU e]) @ (t @ x)).
  exact (map [eqTU @ y] (Dmap t e)).
Defined.
Next Obligation.
  simpl. unfold prod_eq1'_obligation_1.
  eapply composition. apply comp. apply identity. eapply (map2 [eqTU @ x]). apply (Dmap_id t).
  unfold transport_id in *.
  pose (eq:= @nat_trans_id A T U eqTU x (t @ x)).
  simpl in eq.  
  eapply composition in eq. Focus 2.
  simpl_id_bi.
  eapply inverse in eq. eapply composition in eq. Focus 2.
  eapply inverse. eapply composition. simpl_id.
  eapply composition.
  apply comp. apply identity. unfold id. apply (inv_id ([eqTU @ x] @ (t @ x))).
  simpl_id. apply identity. 
  apply inv_left_right. exact eq.
Defined.
Next Obligation.
  simpl. unfold prod_eq1'_obligation_1.
  unfold transport_map, transport_comp.
  assert (eq:= nat_trans_comp eqTU x y z e e' (t @ x)).
  simpl in eq.
  eapply composition in eq. Focus 2.
  simpl_id_bi. 
  eapply inverse in eq. eapply composition in eq. Focus 2.
  simpl_id_bi.
  apply inv_left_right. 
  eapply composition. eapply (map2 [eqTU @ z]). apply (Dmap_comp t).
  eapply composition. apply (map_comp [eqTU @ z]).
  eapply inverse. eapply composition. apply assoc.
  eapply composition. apply comp. eapply inverse. apply eq.
  apply identity. clear eq.
  unfold transport_comp, transport, transport_map.
  eapply composition. apply assoc.
  eapply composition. apply comp. eapply composition.
  apply comp. apply assoc.
  apply (map_comp [map U e']).
  eapply composition. apply assoc.
  eapply composition. apply comp.
  eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp.  apply identity.
  eapply composition. eapply inverse.
  apply (map_comp [map U e']).
  eapply composition. eapply (map2 [map U e']).
  apply inv_L. apply (map_id [map U e']).
  apply id_L. apply identity. apply identity. apply identity.
  eapply inverse. eapply composition.  apply comp. apply identity.
  apply (map_comp [eqTU @ z]). eapply composition. apply assoc.
  eapply inverse. eapply composition. apply assoc.
  apply comp; try apply identity.
  eapply composition. eapply inverse. apply assoc.
  eapply composition. eapply inverse. apply assoc.
  apply comp; try apply identity.
  eapply (left_simplify' (T:=(|U @ z|g))).
  eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity.
  eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity.
  apply inv_R. apply id_L.
  eapply inverse. apply (α_map [α_map eqTU e']).
Defined.
Next Obligation.
  unfold prod_eq1'_obligation_1. unfold transport_map, transport_eq.
  eapply composition. apply comp. apply identity.
  eapply composition. eapply (map2 [ [eqTU] y]).
  apply (Dmap2 t H).
  eapply (map_comp [ [eqTU] y ]).
  unfold transport_map, transport_eq.
  eapply composition. apply assoc. eapply inverse. eapply composition. apply assoc.
  apply comp; try apply identity.
  eapply left_simplify'. eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity. apply inv_R.
  simpl_id_bi.
  eapply right_simplify'. eapply composition. apply assoc.
  eapply composition. apply comp. eapply composition. apply assoc.
  eapply composition. apply comp. apply inv_L. apply identity. apply id_R.
  apply identity.
  assert (eq := nat_trans2 eqTU x y e e' H (t @ x)).
  simpl in eq. eapply composition in eq. Focus 2.
  simpl_id_bi. eapply inverse in eq. eapply composition in eq. Focus 2.
  simpl_id_bi. apply eq.
Defined.

Program Instance prod_eq2' A (T U : [|A|g --> _Type]) (eqTU : T ~1 U) :
        Functor (λ (t : [_Prod T]), (λ a : [A], [eqTU @ a] @ (t @ a)  ; prod_eq1' A T U eqTU t) : [_Prod U]).
Next Obligation. exists (fun t => map [eqTU @ t] (X @ t)). intros; simpl.
                 unfold _Dmap. simpl. unfold prod_eq1'_obligation_1.
                 red; intros. 
                 eapply composition. eapply inverse. apply assoc.
                 eapply composition. apply comp. apply identity.
                 eapply composition. eapply inverse. apply (map_comp [eqTU @ t']).
                 eapply composition. eapply (map2 [eqTU @ t']). apply (Π2 X).
                 apply (map_comp [eqTU @ t']).
                 unfold transport_map. eapply composition. apply assoc.
                 apply inverse. eapply composition. apply assoc.
                 apply comp; [idtac | apply identity].
                 apply (α_map ((inverse [α_map eqTU e]) : nat_trans _ _)).
Defined.
Next Obligation. intro. simpl. apply (map_comp [eqTU @ t]). Defined.
Next Obligation. intro. simpl. apply (map2 [eqTU @ t]). apply (X _). Defined.
  
Definition prod_eq' A (T U : [|A|g --> _Type]) (e:T ~1 U) : [_Prod T --> _Prod U] := (_ ; prod_eq2' A T U e).
