Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
From Groupoid
Require Import HoTT_light groupoid fun_eq groupoid_interpretation_def
Equiv_adjoint fun_depfun sum_id prod_eq sum_eq.
From Groupoid Require groupoid_interpretation.
From Lambda.TPOSR Require Import Env Terms Types.

Set Universe Polymorphism.
(* Set Program Mode. *)

(** Idea of the theorem: any two interpreted type equality derivations
  between the same types are ~2 related. This is implied by the fact that
  a type equality derivation is always interpreted by an identity isomorphism
  up-to the groupoid laws and congruences of the constructors, plus the 
  computation rules.

  We want to show: 
 *)

(** Typeclass to overload the interpretation brackets. *)
Class Interpretation (A B : Type) :=
  interp : A -> B.
Notation "〚 x 〛" := (interp x).
Notation "〚 x ':>' U 〛" := (interp (B:=U) x).

Fixpoint interp_lenv_aux (l : lenv) (Γ : Context)
         (interp_typ : lterm -> Typ Γ)
         (env : nat -> Typ Γ)
  : Context :=
  match l with
  | nil => Γ
  | cons t l' =>
    let tint : Typ Γ := interp_typ t in
    interp_lenv_aux l' (@_Sum0 Γ tint)
                    (fun x => interp_typ x ⋅⋅ groupoid_interpretation.Sub)
                    (fun x => match x with
                           | 0 => tint ⋅⋅ groupoid_interpretation.Sub
                           | Datatypes.S n => env n ⋅⋅ groupoid_interpretation.Sub
                           end)
  end.

Program Definition interp_lenv (l : lenv) :=
  interp_lenv_aux (rev l) Empty _ _.

Next Obligation.
  
  red. red. red. refine {| proj1 := fun x : [Empty] => Empty |}.
  refine {| _map x y p := identity _ |}; intros; apply identity.
Defined.


Next Obligation.
  red. intros.
  red. red. red. refine {| proj1 := fun x : [Empty] => Empty |}.
  refine {| _map x y p := identity _ |}; intros; apply identity.
Defined.

Instance typ_interpretation Γ : Interpretation lterm (Typ Γ) :=
  fun x : lterm => _. (* FIXME *)
Admitted.

Program Fixpoint interp_type (l : lenv) (t : lterm) :
  option (Typ (interp_lenv l)) :=
  match t with
  | Srt_l s => None
  | Ref_l n => None (* no type quantification allowed *)
  | Abs_l _ _ => None (* not a type *)
  | App_l ann f u => (* f should be a type constructor *)
    None
  | Pair_l _ _ _ => None
  | Prod_l dom codom =>
    match interp_type l dom with
    | Some domty =>
      match interp_type (dom :: l) codom with
      | Some codomty =>
        Some (groupoid_interpretation.Prod (A:=domty) _)
      | _ => None
      end
    | None => None
    end
  | _ => None
  end.
Next Obligation.
  unfold interp_lenv in codomty. simpl in codomty.
  do 3 red. simpl.
  
Qed.
    
                                                                                


Instance ctx_interpretation : Interpretation lenv Context := interp_lenv.

Fixpoint term_interp (l : lenv) (t : lterm) (A : lterm) : Elt (interp_type l A) :=
  match t with
  | Srt_l s => Type1
  | _ => Type1
  end.

Instance term_interpretation {Γ} {A : Typ Γ} : Interpretation lterm (Elt A) :=
    

Axiom typ : Set.
Axiom type_eq : ctx -> typ -> typ -> Prop.

Instance typeq_interpretation (Γ : ctx) (A B : typ) :
  Interpretation (type_eq Γ A B) (eq1 (T:=Typ 〚 Γ 〛) 〚 A 〛 〚 B 〛).
Admitted.






Definition interp_teq Γ (A B : term) (e : Γ |- A = B) :
  〚 A 〛 ~1 〚 B 〛.
            
Definition unicity_of_conversions_stmt :=
  ∀ {Γ} (e e' : Γ |- A = B), interp_teq e ~2 interp_teq e'.

Definition unicity_of_conversions_stmt :=
  forall {Γ} {A B:Typ Γ} (e e' : A ~1 B) : e ~2 e'.
