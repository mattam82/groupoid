Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Require Import Groupoid.HoTT_light.
Require Import Groupoid.groupoid.
Require Import Groupoid.fun_eq.
Require Import Groupoid.groupoid_interpretation_def.
Require Import Groupoid.Equiv_adjoint.
Require Import Groupoid.fun_depfun.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Primitive Projections.
Set Program Mode.
 
Opaque Equiv_adjoint.
Opaque map_inv.

Obligation Tactic := intros.

Instance sum_eq2 (A: [Type0]) (T U : [([[A]]) --> Type0]) (eqTU : T ~1 U) :
        Functor (T:=[[_Sum0 (T:=A) T]]) (U:=[[_Sum0 U]]) 
                (λ a, ([a]; [eqTU @ [a] ] @ (Π2 a))). 
Next Obligation. exists ([X]).
                 eapply composition. Focus 2.
                 apply (map [eqTU @[y] ] (Π2 X)).
                 apply inverse. apply ([α_map eqTU [X] ] @ (eq_section x)).
Defined.
Next Obligation. exists (identity _). apply Trunc_1. Defined.
Next Obligation. exists (identity _). apply Trunc_1. Defined.
Next Obligation. exists [X]. apply Trunc_1. Defined.

Definition sum_eq (A: [Type0]) (T U : [([[A]]) --> Type0]) (e:T ~1 U) : [([[_Sum0 (T:=A) T]]) --> ([[_Sum0 U]])] := (_ ; sum_eq2 A T U e).

Hint Extern 4 (@Composition (@sigma _ Groupoid) Fun_Type) => exact comp_fun : typeclass_instances.
Hint Extern 4 (@HomT2 (@sigma _ Groupoid) Fun_Type) => exact nat_transHom' : typeclass_instances.

Definition sum_eq_comp' (A: [Type0]) (T U V : [([[A]]) --> Type0])
        (e:T ~1 U) (e' : U ~1 V) : 
  ∀ t : [_Sum0 (T:=A) T], [(sum_eq e') ° (sum_eq e)] t ~1 [sum_eq (e' ° e)] t.
intro; simpl. red; simpl. exists (identity _). apply (map_id ([[[V]]])).
Defined.

Definition sum_eq_comp (A: [Type0]) (T U V : [([[A]]) --> Type0])
           (e:T ~1 U) (e' : U ~1 V) : 
  sum_eq e' ° sum_eq e ~ sum_eq (e' °e) := (sum_eq_comp' e e'; _).
Next Obligation. intros t t' X. 
                 exists (inverse (id_R _ _ _) ° id_L _ _ _ ). 
                 apply Trunc_1. 
Defined.

Definition sum_eq_map' (A: [Type0]) (T U : [([[A]]) --> Type0])
        (e e':T ~1 U) (H : e ~ e') (t:[_Sum0 (T:=A) T]) :  
  [sum_eq e] t ~1 [sum_eq e'] t := (identity _; _).
Next Obligation. 
  eapply composition. apply (map_id ([[[U]]])). 
  apply ([H [t] ] @ (Π2 t)).
Defined.

Definition sum_eq_map (A: [Type0]) (T U : [([[A]]) --> Type0])
        (e:T ~1 U) (e' : T ~1 U) (H : e ~ e') : nat_trans (sum_eq e) (sum_eq e') 
:= (sum_eq_map' H; _ ). 
Next Obligation. intros t t' X.
                 exists (inverse (id_R _ _ _) ° id_L _ _ _ ). 
                 apply Trunc_1.
Defined.

Hint Extern 4 (@Identity (@sigma _ Groupoid) _) => exact id_fun : typeclass_instances.

Definition sum_eq_id'  (A: [Type0]) (T : [([[A]]) --> Type0])
 : ∀ t : [_Sum0 T], 
     sum_eq (identity T) @ t ~1 identity ([[_Sum0 (T:=A) T]]) @ t :=
  fun t => (identity _ ;  [map_id ([[[T]]])] @ _).

Definition sum_eq_id  (A: [Type0]) (T : [([[A]]) --> Type0])
 : sum_eq (identity T) ~ identity ([[_Sum0 (T:=A) T]]) 
  := (sum_eq_id' (T:=T); _).
Next Obligation. intros t t' X.
                 exists (inverse (id_R _ _ _) ° id_L _ _ _ ). 
                 apply Trunc_1.
Defined.

Definition sum_eq_iso_section (A: [Type0]) (T U : [([[A]]) --> Type0])
           (e : T ~1 U) :
  sum_eq e ° sum_eq e^-1 ~ identity ([[(_Sum0 (T:=A) U)]]) :=
  (sum_eq_id U ° (@sum_eq_map _ _ _ (e ° e ^-1) (identity U)) _)
    ° sum_eq_comp e ^-1 e.
Next Obligation. intro. apply inv_R. Defined.

Definition sum_eq_iso_retraction (A: [Type0]) (T U : [([[A]]) --> Type0])
           (e : T ~1 U) :
       sum_eq e ^-1 ° sum_eq e ~ identity ([[(_Sum0 (T:=A) T)]]) :=
  (sum_eq_id T ° (@sum_eq_map _ _ _ (e^-1 ° e) (identity T)) _)
    ° sum_eq_comp e e^-1.
Next Obligation. intro. apply inv_L. Defined.

Instance sum_eq_iso (A: [Type0]) (T U : [([[A]]) --> Type0]) (e:T ~1 U) : 
  Iso_struct (sum_eq e) := 
  {| _adjoint := sum_eq e^-1 ; 
     _section := sum_eq_iso_section e;
     _retraction := sum_eq_iso_retraction e |}.

Definition sum_eqT (A: [Type0]) (T U : [([[A]]) --> Type0]) (e:T ~1 U) : 
 [[(_Sum0 (T:=A) T)]] <~> [[(_Sum0 (T:=A) U)]] := IsoToEquiv (sum_eq e; sum_eq_iso e).

(* An other version of sum_eq *)


Definition Sum_eq_ {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y) : 
  nat_trans ([F] x) ([F] y ° [map A e]). 
  eapply composition. 
  eapply inverse. apply nat_id_R.
  eapply composition. apply nat_comp'. 
  eapply inverse. apply (inv_L _ _ (map A e)). apply identity.
  apply (nat_comp' (identity _) (Dmap F e)).
Defined.

Definition Sum_eq_2 {Γ} (A:Typ Γ) (F:TypFam A) {x y : [Γ]} (e:x~1 y) :
 [ _Sum0 (F @ x)] -> [_Sum0 (F @ y)] := 
  fun X => ([map A e] @ [X] ; [Sum_eq_ F e @ [X] ] @ (X.2)).

Instance Sum_eq_3 {Γ} (A:Typ Γ) (F:TypFam A) {x y : [Γ]} (e:x~1 y) :
 Functor (T:=[[_Sum0 (F @ x)]]) (U:=[[_Sum0 (F @ y)]]) (Sum_eq_2 F e).
Next Obligation.
  exists (map [map A e] [X]).  
  eapply composition. apply (inverse (α_map (Sum_eq_ F e) [X])).
  exact (map ([Sum_eq_ F e @ [y0] ]) X.2).
Defined.
Next Obligation. exists (map_id [map A e]). apply Trunc_1. Defined.
Next Obligation. exists (map_comp [map A e] [e0] [e']). apply Trunc_1. Defined.
Next Obligation. exists (map2 [map A e] [X]). apply Trunc_1. Defined.

Definition Sum_eq {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y):
 [[_Sum0 (F @ x) ]] ---> [[_Sum0 (F @ y) ]] := (_; Sum_eq_3 A F e).

Definition Sum_eq_comp' {Γ} (A:Typ Γ) (F:TypFam A) {x y z: [Γ]}
        (e:x~1 y) (e' : y ~1 z) t: 
  (Sum_eq F e' ° Sum_eq F e) @ t~1 Sum_eq F (e' °e) @ t.
  exists (inverse [map_comp A e e'] @ [t]). simpl. 
  unfold id, transport. simpl. apply inverse. eapply composition.
  apply ([map_id (F @ z)]). 
  simpl. unfold id. eapply composition. 
  apply (Dmap_comp F e e'). simpl. unfold id. 
  apply (Equiv_injective (map (F @ z) ([(map_comp A) e e'] @ [t]))).
  eapply composition.  eapply inverse. 
  apply (α_map (Dmap F e')).
  apply inverse. eapply composition. eapply (map [map (F @ z) ([(map_comp A) e e'] @ [t])]).
  apply (map_inv (F @ z)). eapply composition.
  apply [inv_R _ _  (map (F @ z) ([(map_comp A) e e'] @ [t]))].1.
  simpl. unfold id. eapply composition. apply (map_id (F @ z)). 
  simpl; unfold id. apply (map [Dmap F e' @ ([map A e'] @ ([map A e] @ [t]))]).
  pose  ((retraction (map A e') @ ([map A e] @ [t])) ^-1).
  pose (map (adjoint (map A e')) ([(map_comp A) e e'] @ [t])).
  simpl in *. unfold id in e0. 
  pose (@comp _ category_fun _ _ _ _ _ _ _ (identity (adjoint (map A e'))) (Dmap F e)). 
  pose ([@_α_map _ _ _ _ _ e2.2 _ _ ([(map_comp A) e e'] @ [t])].1). 
  eapply composition. eapply (map [map (F @ y) e0]). apply (map_id (F @ y)). simpl; unfold id.
  eapply composition. eapply inverse. apply (α_map (Dmap F e)).
  simpl in e3. apply inverse. eapply composition.
  eapply (map [map (F @ y) _]). eapply inverse. apply (map_id (F @ y)).
  eapply composition. eapply inverse. apply e3. clear e3 e2.
  eapply composition. apply (map_id (F @ y)). simpl; unfold id.
  apply (map [Dmap F e @ (adjoint (map A e') @ ([map A e'] @ ([map A e] @ [t])))]).
  eapply composition. eapply inverse. apply (map_comp (F @ x)).
  eapply composition. eapply inverse. apply (map_comp (F @ x)).
  apply inverse.  eapply composition. eapply inverse. apply (map_comp (F @ x)).
  apply (map2 (F @ x)). apply Trunc_1.
Defined.

Ltac apply Trunc_1_arg t :=   match goal with
    | [ |- ?e ~ ?e'] =>
      let X := fresh in
      let X':=fresh in 
      set(X:=e) in *; 
      set(X':=e') in *; 
      let H := fresh in
      assert (H:=@HoTT_light.center _ (Trunc_1 t _ _ X X'));
      try ((destruct H; apply identity)
             || (simpl in *; destruct H; apply identity))          
  end.


Definition Sum_eq_comp {Γ} (A:Typ Γ) (F:TypFam A) {x y z: [Γ]}
        (e:x~1 y) (e' : y ~1 z) : 
  (Sum_eq F e' ° Sum_eq F e) ~ Sum_eq F (e' °e):=
  (Sum_eq_comp' F e e' ; _).
Next Obligation. red. intros. apply Trunc_1.
Defined.

Definition Sum_eq_map' {Γ} (A:Typ Γ) (F:TypFam A) {x y: [Γ]}
           (e e':x ~1 y) (H : e ~ e') t :
  Sum_eq F e @ t ~1 Sum_eq F e' @ t .
  exists ([map2 A H] @ [t]). simpl.  apply inverse. eapply composition.
  apply (map_id (F @ y)). simpl; unfold id. 
  apply inverse. eapply composition. unfold transport. 
  eapply (map [map (F @ y) _]). apply (map_id (F @ y)).
  simpl. eapply composition. eapply (map [map (F @ y) _]).
  apply (Dmap2 F H). simpl; unfold id. 
  apply (Equiv_injective (map (F @ y) ([(map2 A) H] @ [t])^-1)).
  eapply composition. apply (map_inv (F @ y)). eapply composition. 
  apply [inv_L _ _  (map (F @ y) ([(map2 A) H] @ [t]))].1.
  apply inverse. eapply composition. eapply inverse. apply (α_map (Dmap F e')). simpl.
  apply (map [Dmap F e' @ ([map A e] @ [t])]).
  eapply composition. eapply inverse. apply (map_comp (F @ x)).
  apply inverse. eapply composition. eapply inverse. apply (map_comp (F @ x)).
  apply (map2 (F @ x)). apply Trunc_1. 
Defined.

Definition Sum_eq_map {Γ} (A:Typ Γ) (F:TypFam A) {x y: [Γ]}
        (e e':x ~1 y) (H : e ~ e') :  Sum_eq F e ~1 Sum_eq F e' :=
  (Sum_eq_map' F _ _ H ; _).
Next Obligation. red. intros. apply Trunc_1. Defined.

Definition Sum_eq_id' {Γ} (A:Typ Γ) (F:TypFam A) {x: [Γ]} t
  :  Sum_eq F (identity x) @ t  ~1 identity ([[_Sum0 (F @ x)]]) @t.
  exists ([map_id A] @ [t]). simpl. unfold id, transport.
  eapply composition. eapply (map [map ([[[F @ x]]]) ([map_id A] @ [t])]).
  eapply composition. apply (map_id (F @ x)). apply (Dmap_id F).
  simpl; unfold id.  eapply composition. eapply inverse. apply (map_comp (F @ x)).
  eapply composition. eapply inverse. apply (map_comp (F @ x)).
  eapply composition. Focus 2. apply (map_id (F @ x)).
  apply (map2 (F @ x)). apply Trunc_1.
Defined.

Definition Sum_eq_id {Γ} (A:Typ Γ) (F:TypFam A) {x: [Γ]}
  :  Sum_eq F (identity x) ~1 identity _ :=
  (Sum_eq_id' F ; _).
Next Obligation. red. intros. apply Trunc_1. Defined.

Definition Sum_eq_iso_section  {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y) :
  Sum_eq F e ° Sum_eq F e^-1 ~ identity ([[_Sum0 (F @ _)]])
:=
  (Sum_eq_id F ° (@Sum_eq_map _ _ _ _ _ (e ° e ^-1) (identity _)) _)
    ° Sum_eq_comp F e ^-1 e.
Next Obligation. apply inv_R. Defined.

Definition Sum_eq_iso_retraction {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y) :
  Sum_eq F e^-1 ° Sum_eq F e ~ identity ([[_Sum0 (F @ _)]])
:=
  (Sum_eq_id F ° (@Sum_eq_map _ _ _ _ _ (e ^-1 ° e) (identity _)) _)
    ° Sum_eq_comp F e e^-1.
Next Obligation. apply inv_L. Defined.

Instance Sum_eq_iso {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y) :
  Iso_struct (Sum_eq F e) :=
  {| _adjoint := Sum_eq F e^-1 ;
     _section := Sum_eq_iso_section F e;
     _retraction := Sum_eq_iso_retraction F e |}.

Definition Sum_eqT {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y):
  [[_Sum0 (F @ x)]] <~> [[_Sum0 (F @ y)]] := IsoToEquiv (Sum_eq F e; Sum_eq_iso _ F e).

