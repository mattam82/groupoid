Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
<<<<<<< HEAD
=======
(*Require Import Setoid.*)
>>>>>>> 75e850895a47d4c8084f3e518818383c704ed8ec
Require Import groupoid.

Set Universe Polymorphism.
Set Implicit Arguments.
Set Program Mode.

Set Primitive Projections.

Opaque map_id map_inv Dmap_id.
 
(******* Groupoud_utility **********)

Program Instance left_comp_1 A B C (f: [A --> B]) : WeakFunctor (λ g : [B --> C], g ° f : [A-->C]).
Next Obligation. exists (fun t => X @ (f @ t)). econstructor. 
                 intros. apply (α_map X). Defined.
Next Obligation. unfold left_comp_1_obligation_1. simpl.
                 exact (fun t => identity _). Defined.
Next Obligation. unfold left_comp_1_obligation_1. simpl.
                 exact (fun t => X (f @ t)). Defined.

Program Definition left_comp A B C (f: [A --> B]) : (B --> C) ---> (A --> C) :=
  (fun g => g ° f; left_comp_1 _ _ _ _).

Program Instance right_comp_1 A B C (g: [B --> C]) : WeakFunctor (λ f : [A --> B], g ° f : [A-->C]).
Next Obligation. exists (fun t => map g (X @ t)). econstructor. 
                 intros. simpl. unfold groupoid.arrow_comp_obligation_1. 
                 eapply composition. eapply inverse. apply (map_comp g).
                 eapply inverse. eapply composition. eapply inverse. apply (map_comp g).
                 eapply inverse. apply (map2 g (α_map X e)). Defined.
Next Obligation. unfold right_comp_1_obligation_1. simpl.
                 exact (fun t => map_comp g (e @ t) (e' @ t)). Defined.
Next Obligation. unfold right_comp_1_obligation_1. simpl.
                 exact (fun t => map2 g (X t)). Defined.

Program Definition right_comp A B C (g: [B --> C]) : (A --> B) ---> (A --> C) :=
  (fun f => g ° f; right_comp_1 _ _ _ _).

Definition fun_eq {T T' U U' : [_Type]} (e:T ~1 T') (e': U ~1 U') : 
  (T --> U) ---> (T' --> U') := right_comp T' [e'] ° left_comp U (adjoint e).

Definition right_comp_eq (T T' U : [_Type]) (f f':[T --> T'])
           (H : f ~2 f')  : right_comp U f ~2 right_comp U f'.
exists (fun g => nat_comp' (identity g) H). econstructor.
intros; simpl. red. simpl. intro. simpl_id_bi. eapply inverse. apply (α_map H). 
Defined.

Definition right_comp_eq' (T T' T'' U : [_Type]) (f:[T --> T']) (f' :[T' --> T''])
           : right_comp U (f' ° f) ~2 right_comp U f' ° right_comp U f.
exists (fun g => nat_assoc g f f'). econstructor.
intros; simpl. red. intro. simpl. simpl_id_bi. Defined.

Definition left_comp_eq (T U U' : [_Type]) (g g':[U --> U'])
           (H : g ~2 g')  : left_comp T g ~2 left_comp T g'.
exists (fun f => nat_comp' H (identity f)). econstructor.
intros; simpl. red. simpl. intro. simpl_id_bi. apply (α_map e).
Defined.

Definition nat_assoc_inv (T U U' U'' : [_Type]) (g:[U --> U']) (g' :[U' --> U'']) (f : U'' ---> T) :
  (f ° (g' ° g)) ~1 ((f ° g') ° g).
  eapply inverse. refine (nat_assoc g g' f). Defined.

Definition left_comp_eq' (T U U' U'' : [_Type]) (g:[U --> U']) (g' :[U' --> U'']) 
           : left_comp T (g' ° g) ~2 left_comp T g ° left_comp T g'.
  exists (nat_assoc_inv g g'). econstructor. intros.
  simpl. intro. simpl. simpl_id_bi. apply identity. Defined.

Definition right_left_comp (T T' U U' : [_Type]) (g :[T --> T']) (f: [U --> U'])
           : right_comp T f ° left_comp U g ~1 left_comp U' g ° right_comp T' f.
simpl. red. simpl. exists (fun t => nat_assoc_inv g t f).  econstructor. intros.
  simpl. intro. simpl. simpl_id_bi. apply identity. Defined.

Definition left_comp_id (T U : [_Type]) : left_comp T (identity U) ~2 identity _.
  exists (fun t => nat_id_R t). econstructor. intros. simpl. 
  intro. simpl. simpl_id_bi. Defined.

Definition right_comp_id (T U : [_Type]) : right_comp U (identity T) ~2 identity _.
  exists (fun t => nat_id_L t). econstructor. intros. simpl. 
  intro. simpl. simpl_id_bi. Defined.

Program Instance fun_eq2 (T T' U U' : [_Type]) (e:T ~1 T') (e': U ~1 U') : Iso_struct (fun_eq e e').
Next Obligation. exact (right_comp T (adjoint e') ° left_comp U' [e]). Defined.
Next Obligation. unfold fun_eq, fun_eq2_obligation_1. eapply composition. 
                 apply nat_assoc. eapply composition.  apply nat_comp'. apply nat_comp'.
                 apply right_left_comp. apply identity. apply identity. 
                 eapply composition. apply nat_comp'. eapply composition. eapply inverse. apply nat_assoc.
                 eapply composition. 
                 apply nat_comp'. apply identity. eapply composition. eapply inverse. apply left_comp_eq'.
                 eapply composition. apply left_comp_eq. apply (section e). apply left_comp_id.
                 apply nat_id_L. apply identity. eapply composition. eapply inverse. apply right_comp_eq'.
                 eapply composition. apply right_comp_eq. apply (section e'). apply right_comp_id.
                 Defined.
Next Obligation. unfold fun_eq, fun_eq2_obligation_1. eapply composition. 
                 apply nat_assoc. eapply composition.  apply nat_comp'. apply nat_comp'.
                 apply right_left_comp. apply identity. apply identity. 
                 eapply composition. apply nat_comp'. eapply composition. eapply inverse. apply nat_assoc.
                 eapply composition. 
                 apply nat_comp'. apply identity. eapply composition. eapply inverse. apply left_comp_eq'.
                 eapply composition. apply left_comp_eq. eapply inverse. apply (inverse (retraction e)). apply left_comp_id.
                 apply nat_id_L. apply identity. eapply composition. eapply inverse. apply right_comp_eq'.
                 eapply composition. apply right_comp_eq. eapply inverse. apply (inverse (retraction e')). apply right_comp_id.
                 Defined.

Definition fun_eqT (T T' U U' : [_Type]) (e:T ~1 T') (e': U ~1 U') : (T --> U) ~1 (T' --> U')
  := IsoToEquiv (fun_eq e e'; fun_eq2 _ _ _ _ _ _).

Definition fun_eq_eq (T T' U U' : [_Type]) (e e':T ~1 T') (f f': U ~1 U')
           (H : e ~2 e') (H' : f ~2 f') : fun_eq e f ~1 fun_eq e' f' :=
nat_comp' (left_comp_eq _ (Equiv_adjoint [H])) (right_comp_eq _ [H']).

Definition fun_eq_eq' (T T' T'' U U' U'' : [_Type]) (e:T ~1 T') (e':T' ~1 T'') 
           (f : U ~1 U') (f' : U' ~1 U'') : 
  fun_eq (e' ° e) (f' ° f) ~1 fun_eq e' f' ° fun_eq e f.
eapply composition. apply nat_comp'. apply left_comp_eq'. apply right_comp_eq'.
eapply composition. apply nat_assoc. eapply inverse.
eapply composition. apply nat_assoc. apply nat_comp'; try apply identity.
eapply composition. eapply inverse. apply nat_assoc. eapply inverse.
eapply composition. eapply inverse. apply nat_assoc. apply nat_comp'; try apply identity.
apply right_left_comp. Defined.

Program Definition fun_eq_map {Γ : [_Type]} (A: [Γ --> _Type]) (x y z : [Γ]) (e : x ~1 y) (e' : y ~1 z) :
  fun_eq (map A (e' ° e)) (identity _Type) ~1
  fun_eq (map A e') (identity _Type) ° fun_eq (map A e) (identity _Type).
eapply composition. apply fun_eq_eq. apply (map_comp A). eapply inverse.
apply (id_R (CategoryP:=Equiv_cat)).
apply fun_eq_eq'. Defined.

Program Definition fun_eq_id {Γ : [_Type]} (A: [Γ --> _Type]) (x : [Γ]) :
  fun_eq (map A (identity x)) (identity _Type) ~1
  identity _.
eapply composition. apply fun_eq_eq. apply (map_id A). apply identity. 
unfold fun_eq. eapply composition. apply nat_comp'. apply left_comp_id. 
apply right_comp_id. apply nat_id_L. Defined.

Lemma nat_trans_comp (A: [_Type]) (T U : [A --> _Type]) (α : T ~1 U)
  (x y z  : [A]) (e : x ~1 y) (e' : y ~1 z) :
  (identity _ ** map_comp U e e') ° α_map α (e' ° e) ~2
     inverse (assoc'') ° (α_map α e ** identity _ ) ° assoc'' °
     (identity _ ** α_map α e') ° inverse (assoc'') °
     (map_comp T e e' ** identity _).
Admitted.
  (* trunc_eq. Qed.  *)

Lemma nat_trans_id (A: [_Type]) (T U : [A --> _Type]) (α : T ~1 U)
  (x : [A]) :
       (identity _ ** map_id U) ° α_map α (identity _) ~2 
       inverse (id_L' _) ° id_R' _ ° (map_id T (x:=x) ** identity _).
Admitted.
(* trunc_eq. Defined. *)

Lemma nat_trans2 (A: [_Type]) (T U : [A --> _Type]) (α : T ~1 U)
  (x y : [A]) (e e' : x ~1 y) (H : e ~e') :
  (identity _ ** (map2 U H)) ° (α_map α e) ~ (α_map α e') ° ((map2 T H) ** identity _).
Admitted.
(* trunc_eq. Defined. *)

Program Instance prod_eq1 (A: [_Type]) (T U : [A --> _Type]) (eqTU : T ~1 U)
        (t : [_Prod T]) :
        WeakDependentFunctor U (λ a : [A], [eqTU @ a] @ (t @ a)).
Next Obligation.
  eapply composition.
  exact ((inverse [α_map eqTU e]) @ (t @ x)).
  exact (map [eqTU @ y] (Dmap t e)).
Defined.
Next Obligation.
  unfold prod_eq1_obligation_1. simpl. 
  unfold eq_rect_comp, eq_rect, eq_rect_map. 
  assert (foo := nat_trans_comp eqTU x y z e e' (t @ x)). 
  simpl in foo. unfold groupoid.arrow_comp_obligation_1, id in foo.
  eapply composition in foo. Focus 2.
  simpl_id_bi.
  eapply inverse in foo. eapply composition in foo. Focus 2.
  simpl_id_bi.
  eapply right_simplify'. eapply composition. apply assoc.
  eapply composition. apply comp. apply inv_L. apply identity.
  eapply composition. apply id_R.
  eapply composition. eapply (map2 [eqTU @ z]). apply (Dmap_comp t).
  eapply composition. apply (map_comp [eqTU @ z]). 
  eapply inverse. eapply composition. apply assoc.
  eapply composition. apply comp. eapply inverse. apply foo. 
  apply identity. clear foo.
  unfold eq_rect_comp, eq_rect, eq_rect_map. simpl.
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
  eapply composition. eapply _map2.
  apply inv_L. apply map_id.
  apply id_L. apply identity. apply identity. apply identity.
  eapply inverse. eapply composition.  apply comp. apply identity.
  apply (map_comp [eqTU @ z]). eapply composition. apply assoc.
  eapply inverse. eapply composition. apply assoc.
  apply comp; try apply identity.
  eapply composition. eapply inverse. apply assoc.
  eapply composition. eapply inverse. apply assoc.
  apply comp; try apply identity.
  eapply left_simplify'. eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity. 
  eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity. 
  apply inv_R. apply id_L.
  eapply inverse. apply (α_map [α_map eqTU e']).
Defined.
Next Obligation.
  unfold prod_eq1_obligation_1. unfold eq_rect_eq, eq_rect.
  eapply composition. apply comp. apply identity.
  eapply composition. eapply (map2 [[eqTU] y]).
  apply (Dmap2 t H).
  eapply (map_comp [[eqTU] y]).
  unfold eq_rect_eq, eq_rect.
  eapply composition. apply assoc. eapply inverse. eapply composition. apply assoc.
  apply comp; try apply identity.
  eapply left_simplify'. eapply composition. eapply inverse. apply assoc.
  eapply composition. apply comp. apply identity. apply inv_R.
  simpl_id_bi.
  eapply right_simplify'. eapply composition. apply assoc.
  eapply composition. apply comp. eapply composition. apply assoc. 
  eapply composition. apply comp. apply inv_L. apply identity. apply id_R.
  apply identity.
  assert (foo := nat_trans2 eqTU x y e e' H (t @ x)). 
  simpl in foo. eapply composition in foo. Focus 2.
  simpl_id_bi. eapply inverse in foo. eapply composition in foo. Focus 2.
  simpl_id_bi. apply foo.
Defined.

Program Instance prod_eq2 (A: [_Type]) (T U : [A --> _Type]) (eqTU : T ~1 U) :
        WeakFunctor (λ (t : [_Prod T]), (λ a : [A], [eqTU @ a] @ (t @ a)  ; prod_eq1 A T U eqTU t) : [_Prod U]).
Next Obligation. exists (fun t => map [[eqTU] t] (X @ t)). intros; simpl.
                 unfold _Dmap. simpl. unfold prod_eq1_obligation_1.
                 econstructor; intros.
                 eapply composition. eapply inverse. apply assoc.
                 eapply composition. apply comp. apply identity.
                 eapply composition. eapply inverse. apply (map_comp [eqTU @ t']).
                 eapply composition. eapply (map2 [eqTU @ t']). apply (Π2 X).
                 apply (map_comp [eqTU @ t']). 
                 unfold eq_rect_map. eapply composition. apply assoc.
                 apply inverse. eapply composition. apply assoc.
                 apply comp; [idtac | apply identity].
                 apply (α_map ((inverse [α_map eqTU e]) : nat_trans _ _)). Defined.
Next Obligation. intro. simpl. apply _map_comp. Defined.
Next Obligation. intro; simpl. apply _map2. apply (X _). Defined.
  
Program Definition prod_eq (A: [_Type]) (T U : [A --> _Type]) (e:T ~1 U) : [_Prod T --> _Prod U] := (_; prod_eq2 A T U e).

Program Definition prod_eq_comp' (A: [_Type]) (T U V: [A --> _Type]) 
        (e:T ~1 U) (e' : U ~1 V) : 
  ∀ t : [_Prod T], [prod_eq e' ° prod_eq e] t ~1 [prod_eq (e' ° e)] t.
intro; simpl. red; simpl. exists (fun t => identity _). intros. econstructor; intros.
unfold eq_rect_map. simpl_id_bi. simpl. unfold  prod_eq1_obligation_1. simpl. simpl_id_bi.
unfold groupoid.arrow_comp_obligation_1, eq_rect.
simpl. unfold prod_eq1_obligation_1.
eapply composition. apply comp. apply identity. apply _map_comp. 
eapply composition. apply assoc. apply comp; [idtac | apply identity].
apply inverse. eapply composition. eapply inverse, comp_inv. 
apply comp. apply identity. eapply inverse, map_inv. Defined.

Program Definition prod_eq_comp (A: [_Type]) (T U V: [A --> _Type]) 
        (e:T ~1 U) (e' : U ~1 V) : prod_eq e' ° prod_eq e ~ prod_eq (e' °e).
exists (prod_eq_comp' e e'). econstructor. intros. simpl. red. intros. simpl.
simpl_id_bi. Defined.

Program Definition prod_eq_map' (A: [_Type]) (T U: [A --> _Type]) 
        (e e':T ~1 U) (H : e ~ e') (t:[_Prod T]) :  
  [prod_eq e] t ~1 [prod_eq e'] t.
simpl; red; simpl. exists (fun t0 => [H t0] @ (t @ t0)). econstructor; intros; simpl.
unfold eq_rect_map. simpl. unfold prod_eq1_obligation_1.
simpl. eapply composition. eapply inverse. apply assoc. 
eapply composition. apply comp. apply identity. apply (α_map [H t']).
eapply composition. apply assoc. apply inverse.
eapply composition. apply assoc. apply comp; [idtac | apply identity].
admit.
Defined.

Program Definition prod_eq_map (A: [_Type]) (T U: [A --> _Type]) 
        (e:T ~1 U) (e' : T ~1 U) (H : e ~ e') : prod_eq e ~ prod_eq e'.
simpl; red. exists (prod_eq_map' H). econstructor. intros. simpl. red. intros. simpl.
 apply (α_map [H t0]). Defined.

Program Definition prod_eq_id' (A: [_Type]) (T: [A --> _Type]) :
∀ t : [_Prod T], [prod_eq (identity T)] t ~1 [identity (_Prod T)] t.
intro; exists (fun _ => identity _). econstructor; intros; simpl. unfold id; simpl_id_bi.
unfold prod_eq1_obligation_1, id, eq_rect_map. simpl. 
simpl_id_bi. simpl_id. apply identity. Defined.

Program Definition prod_eq_id (A: [_Type]) (T: [A --> _Type]) 
: prod_eq (identity T) ~ identity _.
exists (prod_eq_id' (T:=T)). econstructor. intros. simpl. red. intros. simpl.
simpl_id_bi. Defined.

Program Instance prod_eq_iso (A: [_Type]) (T U : [A --> _Type]) (e:T ~1 U) : 
  Iso_struct (prod_eq e).
Next Obligation. exact (prod_eq (inverse e)). Defined.
Next Obligation. eapply composition. apply prod_eq_comp. 
                 eapply composition; [idtac | apply prod_eq_id]. 
                 apply prod_eq_map. 
                 intro. simpl. apply equiv_inv_R. 
Defined.
Next Obligation. eapply composition. apply prod_eq_comp. 
                 eapply composition; [idtac | apply prod_eq_id]. 
                 apply prod_eq_map. 
                 intro. simpl. apply equiv_inv_L. 
Defined.

Program Definition prod_eqT (A: [_Type]) (T U : [A --> _Type]) (e:T ~1 U) : 
  _Prod T <~> _Prod U := IsoToEquiv (prod_eq e; prod_eq_iso _ _ _ e).

Program Instance fun_todep_fun_2 (T U: [_Type]) : WeakFunctor (λ _ : [T], U).
Next Obligation. apply identity. Defined.
Next Obligation. unfold fun_todep_fun_2_obligation_1. eapply inverse. 
                 assert (foo := id_L U U (identity U)). apply foo. Defined.
Next Obligation. unfold fun_todep_fun_2_obligation_1. apply identity. Defined. 

Program Definition fun_todep_fun_1 (T U: [_Type]) : [T --> _Type] := 
  (λ _ : [T], U; fun_todep_fun_2  _ _).

Program Instance fun_todep_fun1 (T U: [_Type]) (M : [T --> U]) : WeakDependentFunctor (fun_todep_fun_1 T U) [M].
Next Obligation. unfold id; apply (map M e). Defined.
Next Obligation. unfold fun_todep_fun1_obligation_1, fun_todep_fun_1, fun_todep_fun_2. 
                 eapply composition. apply (map_comp M e e').
                 eapply inverse. eapply composition. apply assoc. apply comp; try apply identity.
                 unfold id. unfold eq_rect_map. simpl. unfold groupoid.arrow_id_obligation_1.
                 eapply composition; try apply id_R.  apply comp; try apply identity.
                 apply inv_id. Defined.
Next Obligation. unfold fun_todep_fun1_obligation_1, fun_todep_fun_1, fun_todep_fun_2. 
                 eapply composition. apply (map2 M H). eapply inverse. apply id_R. Defined.

Program Definition fun_todep_fun (T U: [_Type]) (M : [T --> U]) : 
  [_Prod (fun_todep_fun_1 T U)] := ([M]; fun_todep_fun1 _ _ M). 



