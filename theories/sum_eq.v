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
Next Obligation. exists (identity _). trunc1_eq. Defined.
Next Obligation. exists (identity _). trunc1_eq. Defined.
Next Obligation. exists [X]. trunc1_eq. Defined.

Definition sum_eq (A: [Type0]) (T U : [([[A]]) --> Type0]) (e:T ~1 U) : [([[_Sum0 (T:=A) T]]) --> ([[_Sum0 U]])] := (_ ; sum_eq2 A T U e).

Hint Extern 4 (@Composition (@sigma _ GroupoidP) Fun_Type) => exact comp_fun : typeclass_instances.
Hint Extern 4 (@HomT2 (@sigma _ GroupoidP) Fun_Type) => exact nat_transHom' : typeclass_instances.

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
                 trunc1_eq. 
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
                 trunc1_eq.
Defined.

Hint Extern 4 (@Identity (@sigma _ GroupoidP) _) => exact id_fun : typeclass_instances.

Definition sum_eq_id'  (A: [Type0]) (T : [([[A]]) --> Type0])
 : ∀ t : [_Sum0 T], 
     sum_eq (identity T) @ t ~1 identity ([[_Sum0 (T:=A) T]]) @ t :=
  fun t => (identity _ ;  [map_id ([[[T]]])] @ _).

Definition sum_eq_id  (A: [Type0]) (T : [([[A]]) --> Type0])
 : sum_eq (identity T) ~ identity ([[_Sum0 (T:=A) T]]) 
  := (sum_eq_id' (T:=T); _).
Next Obligation. intros t t' X.
                 exists (inverse (id_R _ _ _) ° id_L _ _ _ ). 
                 trunc1_eq.
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
Next Obligation. exists (map_id [map A e]). trunc1_eq. Defined.
Next Obligation. exists (map_comp [map A e] [e0] [e']). trunc1_eq. Defined.
Next Obligation. exists (map2 [map A e] [X]). trunc1_eq. Defined.

Definition Sum_eq {Γ} (A:Typ Γ) (F:TypFam A) {x y  : [Γ]} (e:x~1 y):
 [[_Sum0 (F @ x) ]] ---> [[_Sum0 (F @ y) ]] := (_; Sum_eq_3 A F e).

Definition Sum_eq_comp' {Γ} (A:Typ Γ) (F:TypFam A) {x y z: [Γ]}
        (e:x~1 y) (e' : y ~1 z) t: 
  (Sum_eq F e' ° Sum_eq F e) @ t~1 Sum_eq F (e' °e) @ t.
  exists (inverse [map_comp A e e'] @ [t]). simpl. 
  unfold id, transport. simpl. apply inverse. eapply composition.
  apply ([_map_id (Functor := (F @ z).2) (x:=[map A (e' ° e)] @ [t])]).
  simpl. unfold id. eapply composition. apply ([Dmap_comp F e e' ([map A (e' ° e)] @ [t])]). simpl. unfold id. apply inverse. 
admit.
Defined.

Ltac trunc1_eq_arg t :=   match goal with
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
Next Obligation. red. intros. trunc1_eq_arg (_Sum0 (F @ z)).
Defined.

Definition Sum_eq_map' {Γ} (A:Typ Γ) (F:TypFam A) {x y: [Γ]}
           (e e':x ~1 y) (H : e ~ e') t :
  Sum_eq F e @ t ~1 Sum_eq F e' @ t .
exists ([map2 A H] @ [t]). simpl.  apply inverse. eapply composition.
  apply ([_map_id (Functor := (F @ y).2) (x:=[map A e'] @ [t])]).
  simpl. unfold id. admit.
Defined.

Definition Sum_eq_map {Γ} (A:Typ Γ) (F:TypFam A) {x y: [Γ]}
        (e e':x ~1 y) (H : e ~ e') :  Sum_eq F e ~1 Sum_eq F e' :=
  (Sum_eq_map' F _ _ H ; _).
Next Obligation. red. intros. trunc1_eq_arg (_Sum0 (F @ y)). Defined.

Definition Sum_eq_id' {Γ} (A:Typ Γ) (F:TypFam A) {x: [Γ]} t
  :  Sum_eq F (identity x) @ t  ~1 identity ([[_Sum0 (F @ x)]]) @t.
  exists ([map_id A] @ [t]). simpl. unfold id.
  admit.
Defined.

Definition Sum_eq_id {Γ} (A:Typ Γ) (F:TypFam A) {x: [Γ]}
  :  Sum_eq F (identity x) ~1 identity _ :=
  (Sum_eq_id' F ; _).
Next Obligation. red. intros. trunc1_eq_arg (_Sum0 (F @ x)). Defined.

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

(* Lemma nat_trans_comp (A: [_Type]) (T U : [|A|g --> Type0]) (α : T ~1 U) *)
(*   (x y z  : [A]) (e : x ~1 y) (e' : y ~1 z) : *)
(*   Equiv_eq2 ((identity _ ** map_comp U e e') ° α_map α (e' ° e)) *)
(*      (inverse (assoc'') ° (α_map α e ** identity _ ) ° assoc'' ° *)
(*      (identity _ ** α_map α e') ° inverse (assoc'') ° *)
(*      (map_comp T e e' ** identity _)). *)
(* intro. trunc1_eq. Defined. *)

(* Lemma nat_trans_id (A: [_Type]) (T U : [|A|g --> Type0]) (α : T ~1 U) *)
(*   (x : [A]) : *)
(*   Equiv_eq2  *)
(*     ((identity _ ** map_id U) ° α_map α (identity _)) *)
(*     (inverse (id_L' _) ° id_R' _ ° (@_map_id _ _ ([T]) _ x ** identity _)). *)
(* Proof. intro. trunc1_eq. Defined. *)

(* Lemma nat_trans2 (A: [_Type]) (T U : [|A|g --> Type0]) (α : T ~1 U) *)
(*   (x y : [A]) (e e' : x ~1 y) (H : e ~e') : *)
(*   Equiv_eq2  *)
(*     ((identity _ ** (map2 U H)) ° (α_map α e)) *)
(*     ((α_map α e') ° ((map2 T H) ** identity _)). *)
(* Proof. intro. trunc1_eq. Defined. *)

(* Definition inv_left_right (A:[_Type]) (x y z :[A]) (f : y ~1 z) (g: y ~1 x) (h:x ~1 z) : *)
(*   f ~2 h ° g -> f ° inverse g ~2 h. *)
(* Proof. *)
(*   intro. eapply (@right_simplify' (|A|g)).  *)
(*   eapply composition; try exact X. *)
(*   eapply composition. apply assoc. eapply composition. *)
(*   apply comp. apply inv_L. apply identity. apply id_R. *)
(* Defined. *)

(* Definition inv_left_right' (A:[_Type]) (x y z :[A]) (f : y ~1 z) (g: y ~1 x) (h:x ~1 z) : *)
(*   f ~2 h ° g  -> inverse h ° f ~2 g. *)
(*   intro. eapply (@left_simplify' (|A|g)).  *)
(*   eapply composition; try exact X. *)
(*   eapply composition. eapply inverse. apply assoc. eapply composition. *)
(*   apply comp. apply identity. apply inv_R. apply id_L. *)
(* Defined. *)

(* Instance sum_eq1' (A:[_Type]) (T U : [|A|g --> Type0]) (eqTU : T ~1 U) *)
(*         (t : [_Prod ([[[T]]])]) : *)
(*         DependentFunctor ([[[U]]]) (λ a : [A], [eqTU @ a] @ (t @ a)). *)
(* Next Obligation. *)
(*   eapply composition. *)
(*   exact ((inverse [α_map eqTU e]) @ (t @ x)). *)
(*   exact (map [eqTU @ y] (Dmap t e)). *)
(* Defined. *)
(* Next Obligation. *)
(*   simpl. unfold sum_eq1'_obligation_1. *)
(*   eapply composition. apply comp. apply identity. eapply (map2 [eqTU @ x]). apply (Dmap_id t). *)
(*   unfold transport_id in *. *)
(*   pose (eq:= @nat_trans_id A T U eqTU x (t @ x)). *)
(*   simpl in eq. *)
(*   eapply composition in eq. Focus 2. *)
(*   simpl_id_bi. *)
(*   eapply inverse in eq. eapply composition in eq. Focus 2. *)
(*   eapply inverse. eapply composition. simpl_id. *)
(*   eapply composition. *)
(*   apply comp. apply identity. unfold id. apply (inv_id _ ([eqTU @ x] @ (t @ x))). *)
(*   simpl_id. apply identity. simpl. *)
(*   pose (map [eqTU @ x] ([map_id T] @ (t @ x))). *)
(*   pose ([eqTU @ x] @ ([map T (identity x)] @ (t @ x))). *)
(*   pose (U @ x). *)
(*   apply (inv_left_right ([[U @ x]])). exact eq. *)
(* Defined. *)

(* Next Obligation. *)
(*   simpl. unfold sum_eq1'_obligation_1. *)
(*   unfold transport_map, transport_comp. *)
(*   assert (eq:= nat_trans_comp eqTU x y z e e' (t @ x)). *)
(*   simpl in eq. *)
(*   eapply composition in eq. Focus 2. *)
(*   simpl_id_bi. *)
(*   eapply inverse in eq. eapply composition in eq. Focus 2. *)
(*   simpl_id_bi. *)
(*   apply (inv_left_right ([[U @ z]])). *)
(*   eapply composition. eapply (map2 [eqTU @ z]). apply (Dmap_comp t). *)
(*   eapply composition. apply (map_comp [eqTU @ z]). *)
(*   eapply inverse. eapply composition. apply assoc. *)
(*   eapply composition. apply comp. eapply inverse. apply eq. *)
(*   apply identity. clear eq. *)
(*   unfold transport_comp, transport, transport_map. *)
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
(*   eapply (left_simplify' ([[U @ z]])). *)
(*   eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. apply comp. apply identity. *)
(*   eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. apply comp. apply identity. *)
(*   apply inv_R. apply id_L. *)
(*   eapply inverse. apply (α_map [α_map eqTU e']). *)
(* Defined. *)

(* Next Obligation. *)
(*   unfold sum_eq1'_obligation_1. unfold transport_map, transport_eq. *)
(*   eapply composition. apply comp. apply identity. *)
(*   eapply composition. eapply (map2 [ [eqTU] y]). *)
(*   apply (Dmap2 t H). *)
(*   eapply (map_comp [ [eqTU] y ]). *)
(*   unfold transport_map, transport_eq. *)
(*   eapply composition. apply assoc. eapply inverse. eapply composition. apply assoc. *)
(*   apply comp; try apply identity. *)
(*   eapply left_simplify'. eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. apply comp. apply identity. apply inv_R. *)
(*   simpl_id_bi. *)
(*   eapply right_simplify'. eapply composition. apply assoc. *)
(*   eapply composition. apply comp. eapply composition. apply assoc. *)
(*   eapply composition. apply comp. apply inv_L. apply identity. apply id_R. *)
(*   apply identity. *)
(*   assert (eq := nat_trans2 eqTU x y e e' H (t @ x)). *)
(*   simpl in eq. eapply composition in eq. Focus 2. *)
(*   simpl_id_bi. eapply inverse in eq. eapply composition in eq. Focus 2. *)
(*   simpl_id_bi. apply eq. *)
(* Defined. *)

(* Instance sum_eq2' A (T U : [|A|g --> Type0]) (eqTU : T ~1 U) : *)
(*         Functor (λ (t : [_Prod ([[[T]]])]), (λ a : [A], [eqTU @ a] @ (t @ a)  ; sum_eq1' A T U eqTU t) : [_Prod ([[[U]]])]). *)
(* Next Obligation.  *)
(*   exists (fun t => map [eqTU @ t] (X @ t)). intros; simpl. *)
(*   unfold _Dmap. simpl. unfold sum_eq1'_obligation_1. *)
(*   red; intros.  *)
(*   eapply composition. eapply inverse. apply assoc. *)
(*   eapply composition. apply comp. apply identity. *)
(*   eapply composition. eapply inverse. apply (map_comp [eqTU @ t']). *)
(*   eapply composition. eapply (map2 [eqTU @ t']). apply (Π2 X). *)
(*   apply (map_comp [eqTU @ t']). *)
(*   unfold transport_map. eapply composition. apply assoc. *)
(*   apply inverse. eapply composition. apply assoc. *)
(*   apply comp; [idtac | apply identity]. *)
(*   apply (α_map ((inverse [α_map eqTU e]) : nat_trans _ _)). *)
(* Defined. *)
(* Next Obligation. intro. simpl. apply (map_id [eqTU @ t]). Defined. *)
(* Next Obligation. intro. simpl. apply (map_comp [eqTU @ t]). Defined. *)
(* Next Obligation. intro. simpl. apply (map2 [eqTU @ t]). apply (X _). Defined. *)
  
(* Definition sum_eq' A (T U : [|A|g --> Type0]) (e:T ~1 U) :  *)
(*   [_Prod ([[[T]]]) --> _Prod ([[[U]]])] :=  *)
(*   (_ ; sum_eq2' A T U e). *)
