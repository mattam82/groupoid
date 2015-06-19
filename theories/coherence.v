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

(* Inductive opt {A : Type} : Type := *)
(* | None : opt *)
(* | Some : A -> opt. *)

(* Arguments opt : clear implicits.  *)
Axiom cheat : forall {A}, A.

Definition bind_error {A B} : Exc A -> (A -> Exc B) -> Exc B :=
  fun x f =>
    match x with
    | None => None
    | Some e => f e
    end.

Definition extend_env Γ (env : nat -> option (Typ Γ)) (A : Typ Γ) : nat -> option (Typ (_Sum0 A)) :=
  fun x => match x return _ with
        | 0 => Some (A ⋅⋅ groupoid_interpretation.Sub)
        | Datatypes.S n =>
          bind_error (env n)
                     (fun x => Some (x ⋅⋅ groupoid_interpretation.Sub))
        end. 

(** Universe inconsistency! Of course, the universe level of a context depends on
  the types in it... And interp_type should be first-class polymorphic to interpret
  dependent products. *)
Program
Fixpoint interp_lenv_aux (l : lenv) (Γ : Context) (env : nat -> option (Typ Γ)) {struct l} : Context :=
  match l return _ with
  | nil => Γ
  | cons t l' =>
    let interp_type :=
        let fix interp_type (Γ : Context) (t : lterm) (env : nat -> option (Typ Γ)) {struct t} : option (Typ Γ) :=
      match t return option (Typ Γ) with
      | Srt_l s => None
      | Ref_l n => env n (* no type quantification allowed *)
      | Abs_l _ _ => None (* not a type *)
      | App_l ann f u => (* f should be a type constructor *)
        None
      | Pair_l _ _ _ => None
      | Prod_l dom codom =>
        match interp_type Γ dom env return option (Typ Γ) with
        | Some domty =>
          let env' := extend_env Γ env domty in
          match interp_type (@_Sum0 Γ domty) codom env' return _ with
          | Some codomty =>
            Some (groupoid_interpretation.Prod (A:=domty)
                 (@groupoid_interpretation.LamT Γ domty cheat))
          | _ => None
          end
        | None => None
        end
      | _ => None
      end
    in interp_type
    in
    let tint : option (Typ Γ) := interp_type Γ t env in
    match tint return _ with
    | None => Γ
    | Some tint =>
      interp_lenv_aux l' (@_Sum0 Γ tint) (extend_env Γ env tint)
    end
  end.

Program Definition interp_lenv (l : lenv) :=
  interp_lenv_aux (rev l) Empty (fun x => None).

Instance typ_interpretation Γ : Interpretation lterm (Typ Γ) :=
  fun x : lterm => _. (* FIXME *)
Admitted.

Program Fixpoint interp_type_aux (Γ : Context) (t : lterm) (env : nat -> option (Typ Γ)) {struct t} : option (Typ Γ) :=
  match t return option (Typ Γ) with
  | Srt_l s => None
  | Ref_l n => env n (* no type quantification allowed *)
  | Abs_l _ _ => None (* not a type *)
  | App_l ann f u => (* f should be a type constructor *)
    None
  | Pair_l _ _ _ => None
  | Prod_l dom codom =>
    match interp_type_aux Γ dom env return option (Typ Γ) with
    | Some domty =>
      let env' := extend_env Γ env domty in
      match interp_type_aux (@_Sum0 Γ domty) codom env' return _ with
      | Some codomty =>
        Some (groupoid_interpretation.Prod (A:=domty)
                                           (@groupoid_interpretation.LamT Γ domty cheat))
      | _ => None
      end
    | None => None
    end
  | _ => None
  end.

Definition interp_type (l : lenv) (t : lterm) : option (Typ (interp_lenv l)) :=
  interp_type_aux (interp_lenv l) t (fun x => None).

             
                                                                                


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
