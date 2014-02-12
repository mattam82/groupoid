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

(* Definition fun_id T := identity (Identity := id_fun) T. *)

Hint Extern 4 (@Identity (@sigma _ GroupoidP) _) => exact id_fun : typeclass_instances.

Program Definition prod_eq_id' (A: [_Type]) (T: [|A|g --> Type0])  :
∀ t : [_Prod ([[[T]]])], [prod_eq (identity T)] t ~1 [identity (_Prod ([[[T]]]))] t :=
  fun t => (fun _ => identity _ ;  _). 
Next Obligation. intros a a' Xa; simpl. trunc1_eq.
Defined.

Definition prod_eq_id (A: [_Type]) (T : [|A|g --> Type0]) 
 : prod_eq (identity T) ~ identity _ := (prod_eq_id' (T:=T); _).
Next Obligation. intros t t' e a. simpl. simpl_id_bi. (* apply setoid_irr2. *) Defined.

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

Program Instance fun_todep_fun_2 (T: UGroupoidType) (U:[_Type]): Functor (λ _ : [T], U).
Next Obligation. apply identity. Defined.
Next Obligation. unfold fun_todep_fun_2_obligation_1. eapply inverse.
                 assert (foo := id_L U U (identity U)). apply foo. Defined.
Next Obligation. unfold fun_todep_fun_2_obligation_1. apply identity. Defined.

Program Definition fun_todep_fun_1 (T U : [_Type]) : [|T|g --> _Type] :=
  (λ _ : [T], U; fun_todep_fun_2  _ _).

Program Instance fun_todep_fun1 T (U:[_Type]) (M : [T -||-> U]) : 
  DependentFunctor (fun_todep_fun_1 T U) [M].
Next Obligation. unfold id; apply (map M e). Defined.
Next Obligation. admit. Defined.
Next Obligation. unfold fun_todep_fun1_obligation_1, fun_todep_fun_1, fun_todep_fun_2.
                 eapply composition. apply (map_comp M e e').
                 eapply inverse. eapply composition. apply assoc. apply comp; try apply identity.
                 unfold id. unfold transport_map. simpl. unfold groupoid.arrow_id_obligation_1.
                 eapply composition; try apply id_R.  apply comp; try apply identity.
                 apply (inv_id (M @ x)). Defined.
Next Obligation. unfold fun_todep_fun1_obligation_1, fun_todep_fun_1, fun_todep_fun_2.
                 eapply composition. apply (map2 M H). eapply inverse. apply id_R. Defined.

Definition fun_todep_fun T U (M : [T -||-> U]) :
  [_Prod (fun_todep_fun_1 T U)] := ([M]; fun_todep_fun1 _ _ M).

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
Obligation Tactic := intros.
Next Obligation. exists (fun a => map [Prod_eq_ F e @ a] 
                                      (X @ ([adjoint (map A e)] a))).
                 red; intros. trunc1_eq.
Defined.

Program Instance fun_pi (T U : GroupoidType) (f : T ---> U) : Functor [f] := Π2 f.

Definition map_comp' {T U} (f:T ---> U) {x y z: [T]} (e: x ~1 y) (e':y ~1 z) :=
  map_comp f e e' : map f (e' ° e) ~ map f e' ° map f e.

Next Obligation. intro. intros. simpl. refine (map_comp' _ _ _). Defined.

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
  _Prod ([[[F @ x]]]) <~> _Prod ([[[F @ y]]]) := IsoToEquiv (Prod_eq F e; Prod_eq_iso _ F e).



Ltac mysimpl := 
  simpl (@proj1); simpl (@proj2).

(* This part is not needed for the moment *)

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


Lemma nat_trans_comp (A: [_Type]) (T U : [|A|g --> Type0]) (α : T ~1 U)
  (x y z  : [A]) (e : x ~1 y) (e' : y ~1 z) :
  (identity _ ** map_comp U e e') ° α_map α (e' ° e) ~2
     inverse (assoc'') ° (α_map α e ** identity _ ) ° assoc'' °
     (identity _ ** α_map α e') ° inverse (assoc'') °
     (map_comp T e e' ** identity _).
Proof. intro. trunc_eq'. Defined.

Lemma nat_trans_id (A: [_Type]) (T U : [|A|g --> Type0]) (α : T ~1 U)
  (x : [A]) :
       (identity _ ** map_id U) ° α_map α (identity _) ~2
       inverse (id_L' _) ° id_R' _ ° (map_id T (x:=x) ** identity _).
Proof. intro. trunc_eq'. Defined.

Lemma nat_trans2 (A: [_Type]) (T U : [|A|g --> Type0]) (α : T ~1 U)
  (x y : [A]) (e e' : x ~1 y) (H : e ~e') :
  (identity _ ** (map2 U H)) ° (α_map α e) ~ (α_map α e') ° ((map2 T H) ** identity _).
Proof. intro. trunc_eq'. Defined.


(* Program Instance prod_eq1 (A: [_Type]) (T U : [|A|g --> Type0]) (eqTU : T ~1 U) *)
(*         (t : [Prod0 T]) : *)
(*         DependentFunctor ([[[U]]]) (λ a : [A], [eqTU @ a] @ (t @ a)). *)
(* Next Obligation. *)
(*   eapply composition. *)
(*   exact ((inverse [α_map eqTU e]) @ (t @ x)). *)
(*   exact (map [eqTU @ y] (Dmap t e)). *)
(* Defined. *)
(* Next Obligation. *)
(*   simpl. unfold prod_eq1_obligation_1. *)
(*   eapply composition. apply comp. apply identity. eapply (map2 [eqTU @ x]). apply (Dmap_id t).  *)
(*   unfold transport_id in *. *)
(*   pose (eq:= @nat_trans_id A T U eqTU x). *)
(*   (* assert (map [eqTU @ x] ([map_id ([[[T]]])] @ (t @ x)) *) *)
(*   (*  ° [((α_map eqTU) (identity x))^-1] @ (t @ x) ~ *) *)
(*   (*  [map_id ([[[U]]])] @ ([eqTU @ x] @ (t @ x))). *) *)
(*   (* pose ((proj2 t).(_Dmap_id) x). Dmap_id t). *) *)
(*   (* assert (map [eqTU @ x] (Dmap t (identity x)) *) *)
(*   (*  ° [(α_map eqTU) (identity x)] ^-1 = map [eqTU @ x] (Dmap t (identity x)) *) *)
(*   (*  ° [(α_map eqTU) (identity x)] ^-1). *) *)
(*   admit. *)
(* Defined. *)
(* Next Obligation. *)
(*   simpl. unfold prod_eq1_obligation_1. *)
(*   unfold transport_map, transport_comp. *)
(*   eapply composition. *)
(*   assert (eq:= nat_trans_comp eqTU x y z e e'). *)
(*   eapply composition in eq. Focus 2. *)
(*   simpl_id_bi. *)
(*   eapply inverse in eq. eapply composition in eq. Focus 2. *)
(*   simpl_id_bi.  *)
(*   eapply (right_simplify'). (T:=U @ z)). *)
(*   eapply composition. apply assoc. *)
(*   eapply composition. apply comp. apply inv_L. apply identity. *)
(*   eapply composition. apply id_R. *)
(*   eapply composition. eapply (map2 [eqTU @ z]). apply (Dmap_comp t). *)
(*   eapply composition. apply (map_comp [eqTU @ z]). *)
(*   eapply inverse. eapply composition. apply assoc. *)
(*   eapply composition. apply comp. eapply inverse. apply foo. *)
(*   apply identity. clear foo. *)
(*   unfold eq_rect_comp, eq_rect, eq_rect_map. *)
(*   eapply composition. apply assoc. *)
(*   eapply composition. apply comp. eapply composition. *)
(*   apply comp. apply assoc. *)
(*   apply (map_comp [map U e']). *)
(*   eapply composition. apply assoc. *)
(*   eapply composition. apply comp. *)
(*   eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. apply comp.  apply identity. *)
(*   eapply composition. eapply inverse. *)
(*   apply (map_comp [map U e']). *)
(*   eapply composition. eapply (map2 [map U e']). *)
(*   apply inv_L. apply (map_id [map U e']). *)
(*   apply id_L. apply identity. apply identity. apply identity. *)
(*   eapply inverse. eapply composition.  apply comp. apply identity. *)
(*   apply (map_comp [eqTU @ z]). eapply composition. apply assoc. *)
(*   eapply inverse. eapply composition. apply assoc. *)
(*   apply comp; try apply identity. *)
(*   eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. eapply inverse. apply assoc. *)
(*   apply comp; try apply identity. *)
(*   eapply (left_simplify' (T:=(U @ z))). *)
(*   eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. apply comp. apply identity. *)
(*   eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. apply comp. apply identity. *)
(*   apply inv_R. apply id_L. *)
(*   eapply inverse. apply (α_map [α_map eqTU e']). *)
(* Defined. *)

(* Next Obligation. *)
(*   unfold prod_eq1_obligation_1. unfold transport_map, transport_eq. *)
(*   eapply composition. apply comp. apply identity. *)
(*   eapply composition. eapply (map2 [ [eqTU] y]). *)
(*   apply (Dmap2 t H). *)
(*   eapply (map_comp [ [eqTU] y ]). *)
(*   unfold transport_map, transport_eq.   *)
(*   eapply composition. apply assoc. eapply inverse. eapply composition. apply assoc. *)
(*   apply comp; try apply identity. *)
(*   eapply left_simplify'. eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. apply comp. apply identity. apply inv_R. *)
(*   simpl_id_bi. *)
(*   eapply right_simplify'. eapply composition. apply assoc. *)
(*   eapply composition. apply comp. eapply composition. apply assoc. *)
(*   eapply composition. apply comp. apply inv_L. apply identity. apply id_R. *)
(*   apply identity. *)
(*   assert (foo := nat_trans2 eqTU x y e e' H (t @ x)). *)
(*   simpl in foo. eapply composition in foo. Focus 2. *)
(*   simpl_id_bi. eapply inverse in foo. eapply composition in foo. Focus 2. *)
(*   simpl_id_bi. apply foo. *)
(* Defined. *)

(* Program Instance prod_eq2 (A: UGroupoidType) (T U : [A --> _Type]) (eqTU : T ~1 U) : *)
(*         Functor (λ (t : [_Prod T]), (λ a : [A], [eqTU @ a] @ (t @ a)  ; prod_eq1 A T U eqTU t) : [_Prod U]). *)
(* Next Obligation. exists (fun t => map [[eqTU] t] (X @ t)). intros; simpl. *)
(*                  unfold _Dmap. simpl. unfold prod_eq1_obligation_1. *)
(*                  red; intros. (* apply setoid_irr2. *) *)
(*                  eapply composition. eapply inverse. apply assoc. *)
(*                  eapply composition. apply comp. apply identity. *)
(*                  eapply composition. eapply inverse. apply (map_comp [eqTU @ t']). *)
(*                  eapply composition. eapply (map2 [eqTU @ t']). apply (Π2 X). *)
(*                  apply (map_comp [eqTU @ t']). *)
(*                  unfold eq_rect_map. eapply composition. apply assoc. *)
(*                  apply inverse. eapply composition. apply assoc. *)
(*                  apply comp; [idtac | apply identity]. *)
(*                  apply (α_map ((inverse [α_map eqTU e]) : nat_trans _ _)). *)
(* Defined. *)
(* Next Obligation. intro. (* apply setoid_irr2. *)  *)
(*  simpl. apply (map_comp [eqTU @ t]). Defined. *)
(* Next Obligation. intro. (* apply setoid_irr2. *) simpl. apply (map2 [eqTU @ t]). apply (X _). Defined. *)
  
(* Definition prod_eq (A: UGroupoidType) (T U : [A --> _Type]) (e:T ~1 U) : [_Prod T --> _Prod U] := (_ ; prod_eq2 A T U e). *)
