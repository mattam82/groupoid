Require Export Unicode.Utf8_core.
Require Coq.Program.Tactics.
Require Import HoTT_light groupoid.

Set Universe Polymorphism.
Set Implicit Arguments.
Set Program Mode.

Set Primitive Projections.

Opaque map_id map_inv.
Notation α_map f := ((proj2 f) _ _).

(******* Groupoud_utility **********)

Infix "--->" := Fun_Type (at level 55). 

Program Instance left_comp_1 A B C (f: [A --> B]) : Functor (λ g : [B --> C], g ° f : [A-->C]).
Next Obligation. exists (fun t => X @ (f @ t)). red. 
                 intros. apply (α_map X). Defined.
Next Obligation. unfold left_comp_1_obligation_1. simpl.
                 exact (fun t => identity _). Defined.
Next Obligation. unfold left_comp_1_obligation_1. simpl.
                 exact (fun t => X (f @ t)). Defined.

Program Definition left_comp A B C (f: [A --> B]) : (B --> C) ---> (A --> C) :=
  (fun g => g ° f; left_comp_1 _ _ _ _).

Program Instance right_comp_1 A B C (g: [B --> C]) : Functor (λ f : [A --> B], g ° f : [A-->C]).
Next Obligation. exists (fun t => map g (X @ t)). red.
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

Definition fun_eq {T T' U U': UGroupoidType} (e:T <~> T') (e': U <~> U') : 
  (T --> U) ---> (T' --> U') := right_comp T' [e'] ° left_comp U (adjoint e).

Definition right_comp_eq (T T' U : UGroupoidType) (f f':[T --> T'])
           (H : f ~2 f')  : right_comp U f ~2 right_comp U f'.
exists (fun g => nat_comp' (identity g) H). red.
intros; simpl. red. simpl. intro. simpl_id_bi. eapply inverse. apply (α_map H). 
Defined.

Definition right_comp_eq' (T T' T'' U : UGroupoidType) (f:[T --> T']) (f' :[T' --> T''])
           : right_comp U (f' ° f) ~2 right_comp U f' ° right_comp U f.
exists (fun g => nat_assoc g f f'). red.
intros; simpl. red. intro. simpl. simpl_id_bi. Defined.

Definition left_comp_eq (T U U' : UGroupoidType) (g g':[U --> U'])
           (H : g ~2 g')  : left_comp T g ~2 left_comp T g'.
exists (fun f => nat_comp' H (identity f)). red.
intros; simpl. red. simpl. intro. simpl_id_bi. apply (α_map e).
Defined.

Definition nat_assoc_inv (T U U' U'' : UGroupoidType) (g:[U --> U']) (g' :[U' --> U'']) (f : U'' ---> T) :
  (f ° (g' ° g)) ~1 ((f ° g') ° g).
  eapply inverse. refine (nat_assoc g g' f). Defined.

Definition left_comp_eq' (T U U' U'' : UGroupoidType) (g:[U --> U']) (g' :[U' --> U'']) 
           : left_comp T (g' ° g) ~2 left_comp T g ° left_comp T g'.
  exists (nat_assoc_inv g g'). red. intros.
  simpl. intro. simpl. simpl_id_bi. apply identity. Defined.

Definition right_left_comp (T T' U U' : UGroupoidType) (g :[T --> T']) (f: [U --> U'])
           : right_comp T f ° left_comp U g ~1 left_comp U' g ° right_comp T' f.
simpl. red. simpl. exists (fun t => nat_assoc_inv g t f). red. intros.
  simpl. intro. simpl. simpl_id_bi. apply identity. Defined.

Definition left_comp_id (T U : UGroupoidType) : left_comp T (identity U) ~2 identity _.
  exists (fun t => nat_id_R t). red. intros. simpl. 
  intro. simpl. simpl_id_bi. Defined.

Definition right_comp_id (T U : UGroupoidType) : right_comp U (identity T) ~2 identity _.
  exists (fun t => nat_id_L t). red. intros. simpl. 
  intro. simpl. simpl_id_bi. Defined.

Program Instance fun_eq2 (T T' U U' : UGroupoidType) (e:T <~> T') (e': U <~> U') : Iso_struct (fun_eq e e').
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

Definition fun_eqT (T T' U U' : UGroupoidType) (e:T <~> T') (e': U <~> U') : (T --> U) <~> (T' --> U')
  := IsoToEquiv (fun_eq e e'; fun_eq2 _ _ _ _ _ _).

Definition fun_eq_eq (T T' U U' : UGroupoidType) (e e':T <~> T') (f f': U <~> U')
           (H : Equiv_eq e e') (H' : Equiv_eq f f') : fun_eq e f ~1 fun_eq e' f' :=
nat_comp' (left_comp_eq _ (Equiv_adjoint [H])) (right_comp_eq _ [H']).

Definition fun_eq_eq' (T T' T'' U U' U'' : UGroupoidType) (e:T <~> T') (e':T' <~> T'') 
           (f : U <~> U') (f' : U' <~> U'') : 
  fun_eq (e' ° e) (f' ° f) ~1 fun_eq e' f' ° fun_eq e f.
eapply composition. apply nat_comp'. apply left_comp_eq'. apply right_comp_eq'.
eapply composition. apply nat_assoc. eapply inverse.
eapply composition. apply nat_assoc. apply nat_comp'; try apply identity.
eapply composition. eapply inverse. apply nat_assoc. eapply inverse.
eapply composition. eapply inverse. apply nat_assoc. apply nat_comp'; try apply identity.
apply right_left_comp. Defined.

Definition id_R_groupoid : ∀ (x y : UGroupoidType) (f : x <~> y), Equiv_eq (f ° identity x) f.
  intros. set (H := nat_id_R [f]). exists H. 
  red. intro.
  eapply composition. apply section_comp.
  eapply composition. apply comp. apply (map_id [f]). apply identity.
  eapply inverse. eapply composition. apply comp.
  eapply composition. apply id_R. apply identity. apply identity.
  eapply composition. apply comp. eapply composition. eapply (map2 [f]).
  apply Equiv_adjoint_idR. simpl. apply (map_id [f]). apply identity. 
  apply identity.
Defined.

Program Definition fun_eq_map {Γ : UGroupoidType} (A: [Γ --> _Type]) (x y z : [Γ]) (e : x ~1 y) (e' : y ~1 z) : 
  fun_eq (map A (e' ° e)) (identity _Type) ~1
  fun_eq (map A e') (identity _Type) ° fun_eq (map A e) (identity _Type).
eapply composition. apply fun_eq_eq. apply (map_comp A). eapply inverse.
apply (id_R_groupoid).  (* (CategoryP:=Equiv_cat)). *)
apply fun_eq_eq'. Defined.

Program Definition fun_eq_id {Γ : UGroupoidType} (A: [Γ --> _Type]) (x : [Γ]) :
  fun_eq (map A (identity x)) (identity _Type) ~1
  identity _.
eapply composition. apply fun_eq_eq. apply (map_id A). apply identity. 
unfold fun_eq. eapply composition. apply nat_comp'. apply left_comp_id. 
apply right_comp_id. apply nat_id_L. Defined.

Lemma nat_trans_comp (A: UGroupoidType) (T U : [A --> _Type]) (α : T ~1 U)
  (x y z  : [A]) (e : x ~1 y) (e' : y ~1 z) :
  (identity _ ** map_comp U e e') ° α_map α (e' ° e) ~2
     inverse (assoc'') ° (α_map α e ** identity _ ) ° assoc'' °
     (identity _ ** α_map α e') ° inverse (assoc'') °
     (map_comp T e e' ** identity _).
Proof. (* TODO : nico ? *) admit. Defined.

Lemma nat_trans_id (A: UGroupoidType) (T U : [A --> _Type]) (α : T ~1 U)
  (x : [A]) :
       (identity _ ** map_id U) ° α_map α (identity _) ~2 
       inverse (id_L' _) ° id_R' _ ° (map_id T (x:=x) ** identity _).
Admitted.
(* trunc_eq. Defined. *)

Lemma nat_trans2 (A: UGroupoidType) (T U : [A --> _Type]) (α : T ~1 U)
  (x y : [A]) (e e' : x ~1 y) (H : e ~e') :
  (identity _ ** (map2 U H)) ° (α_map α e) ~ (α_map α e') ° ((map2 T H) ** identity _).
Admitted.
(* trunc_eq. Defined. *)

Ltac simpl_id_end := 
  match goal with
    | [ |- eq2 (?P ^-1 ° ?P) _] => compose;
       [first [apply inv_L | apply equiv_inv_L]|idtac]
    | [ |- eq2 (?P ° ?P ^-1) _] => compose;
       [first [apply inv_R | apply equiv_inv_R]|idtac]
    | [ |- eq2 (?P ° identity ?x) _] => compose;
       [first [apply id_R | apply equiv_id_R]|idtac]
    | [ |- eq2 (identity ?x ° ?P) _] => compose;
       [first [apply id_L | apply equiv_id_L]|idtac]
    | [ |- eq2 ((?P ^-1) ^-1) _] => compose;
       [first [apply inv_inv | apply (@inv_inv _Type)]|idtac]
    | [ |- eq2 ((identity ?T) ^-1) _] => compose;
       [first [apply (inv_id T) | apply (@inv_id _Type)]|idtac]
    | [ |- Equiv_eq (?P ^-1 ° ?P) _] => compose; [apply equiv_inv_L|idtac]
    | [ |- Equiv_eq (?P ° ?P ^-1) _] => compose; [apply equiv_inv_R|idtac]
    | [ |- Equiv_eq (?P ° identity ?x) _] => compose; [apply equiv_id_R|idtac]
    | [ |- Equiv_eq (identity ?x ° ?P) _] => compose; [apply equiv_id_L|idtac]
    | [ |- Equiv_eq ((?P ^-1) ^-1) _] => compose; [apply (@inv_inv _Type)|idtac]
    | [ |- Equiv_eq ((identity _) ^-1) _] => compose; [apply (@inv_id _Type)|idtac]
  end.

Ltac simpl_id_end_extended := first [ simpl_id_end |
                                      match goal with
                   | [ |- Equiv_eq ?e _ ] => apply (identity e)
                   | [ |- eq2 ?e _ ] => apply (identity e)
                   | [ |- _ ] => idtac
                 end].

Ltac simpl_id := first [simpl_id_end ; simpl_id |
  lazymatch goal with
    | |- context [identity _] => fail
    | |- _ => apply identity
  end|
  match goal with
    | [ |- eq2 (?P ^-1) _] =>
      eapply composition;
        [first [apply equiv_inv | apply inv] ; simpl_id | idtac]; 
        try apply identity
    | [ |- eq2 (map ?F (identity _)) _] => 
      eapply composition;
        [eapply (map_id F); simpl_id | idtac]; 
        simpl_id
    | [ |- Equiv_eq (map ?F (identity _)) _] => 
      eapply composition;
        [eapply (map_id F); simpl_id | idtac]; 
        simpl_id
    | [ |- eq2 (map ?F ?P) _] => 
      first [eapply composition;
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
        [first [apply comp |
                apply equiv_comp] ; simpl_id | idtac];
        simpl_id_end_extended
    | [ |- eq2 ?e _ ] => first [has_evar e; idtac | apply (identity e)]
    | [ |- _ ] => idtac
  end].


Ltac simpl_id_bi := simpl_id; eapply inverse; simpl_id.

