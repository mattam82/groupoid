Require Import Utf8 Ssreflect.ssreflect.
Require Import eqtype seq path ssrnat ssrbool ssrfun.  
Require Import ssralg ssrnum ssrint.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Notation min := Num.min. 

Section Assoc.
  Variable dom : eqType.
  Variable codom : Type.

  Definition assoc := dom -> option codom.
  
  Definition finite (a : assoc) := 
    { l : seq dom | forall x, x \notin l -> a x = None }.

  Definition finite_seq (a : assoc) (f : finite a) : seq dom := 
    proj1_sig f.

  Coercion finite_seq : finite >-> seq.

  Implicit Types a : assoc.

  Definition mergef := codom -> codom -> codom.
  
  Definition empty : assoc := fun _ => None.
  Definition add (f : mergef) (a : assoc) (d : dom) (v : codom) :=
    fun k =>
      if k == d then 
        if a k is Some v' then Some (f v v')
        else Some v
      else a k.

  Definition lookup (a : assoc) (d : dom) : option codom := 
    a d.
  
  Variable f : mergef.
  
  Lemma add_empty d v : add f empty d v =1 fun k => if k == d then Some v else None.
  Proof. move=> x. rewrite /add. now case: (x == d). Qed.

  Definition mergeco (v : codom) (res : option codom) : codom :=
    match res with
      | None => v
      | Some v' => f v v'
    end.

  Lemma add_merge g d v : 
    add f g d v =1 fun k => if k == d then Some (mergeco v (g k)) else g k.
  Proof. move=> x. rewrite /add. 
         case: (x == d). 
         + now case: (g x). 
         + done.
  Qed.
  
  Definition mem a d := if a d is Some _ then true else false.

  Definition singleton k v := add f empty k v.

  Definition union (p q : assoc) : assoc :=
    fun k =>
      match p k, q k with
        | None, x => x
        | x, None => x
        | Some v, Some v' => Some (f v v')
      end.

  Definition remove a k := 
    fun k' =>
      if k' == k then None
      else a k'.

  Definition notin_cons x y (l : seq dom) : x \notin (y :: l) -> x \notin l.
  Proof. rewrite in_cons. by move/norP => /= [_ Hl]. Qed.

  Definition in_rem x y (s : seq dom) : x \in rem y s -> x \in s.
  Proof.
    elim: s => [|a tl IH]; move=> // /=. 
    case E: (a == y). 
    - rewrite in_cons. move => ->. apply/orP. by right.
    - rewrite !in_cons. 
      case E: (x == a)=> //. 
  Qed.

  Definition notin_rem x y (s : seq dom) : x \notin s -> x \notin rem y s.
  Proof.
    apply: contra. by apply: in_rem.
  Qed.

  Definition in_diff x y (s : seq dom) : ~~ (x == y) -> x \in s -> x \in rem y s.
  Proof.
    move=> Hxy. elim: s => [|a tl IH] // /=.
    rewrite !in_cons.
    case E: (a == y). 
    - move/orP=> [eqxa|Hi] //. move/eqP: E eqxa=> -> Hxy'. 
        by rewrite Hxy' in Hxy.
    - rewrite in_cons. move/orP=> [->|H] //.
      rewrite (IH H). by rewrite orbT.
  Qed.

  Lemma remove_finite a k : finite a -> finite (remove a k).
  Proof. 
    move=> [l Hl]. exists (rem k l).
    move=> x Hx; rewrite /remove. 
    case: ifPn => E //.
    apply: Hl. move: Hx. apply: contra. 
    by apply in_diff. 
  Defined.

  Lemma remove_finite_notin a k (fin : finite a) : k \notin (finite_seq fin) ->
    (size (remove_finite k fin) <= size fin)%nat.
  Proof.
    by move: fin => [s Hs] /= Hn; rewrite rem_id //.
  Qed.

  Lemma remove_finite_in a k (fin : finite a) : k \in (finite_seq fin) ->
    (size (remove_finite k fin) < size fin)%nat.
  Proof.
    move: fin => [s Hs] /= Hn.
    rewrite size_rem //.
    move: Hn {Hs}.
    case: s => [] Hs. discriminate Hs.
    move=> l Hl; apply leqnn.            
  Qed.

End Assoc.

Section GraphStruct.
  (** Universe levels *)
  Variable L : eqType.
  
  Definition constraint := (L * int * L)%type.
  
  Definition node := assoc L int.
  Definition mergenode : mergef int := min.
  Definition addN : node -> L -> int -> node := add mergenode.

  Definition graph := assoc L node.

  Definition pathelt := (L * int)%type.
  Definition apath := seq pathelt.

  Open Scope seq_scope.
  Open Scope pair_scope.

  Definition weight (p : apath) : int :=
    foldr (fun x y => x.2 + y) (0:int) p.

  Section Paths.
    Variable g : graph.

    Definition path_fn : rel pathelt :=
      fun x y =>
        if g x.1 is Some n then mem n y.1 else false.

    Definition path l p := path path_fn (l, 0) p.
  
    Definition cyclic_path p := 
      ~~ nilp p && cycle path_fn p.

    Definition cyclic := exists p, cyclic_path p.

    Definition positive (p : apath) := 0 < weight p.
    
    Definition poscycle (p : apath) := cyclic_path p && positive p.

    Definition consistent := forall p : apath, ~~ poscycle p.
  End Paths.

  Definition constraints := seq constraint.

  Definition upd (g : graph) (l : L) (k : int) (l' : L) :=
    add (union min) g l (singleton min l' k).

  Definition egraph : graph := empty _. 

  Definition addC (c : constraint) (g : graph) : graph :=
    let '(l,p,l') := c in
      upd g l p l'.

  Definition cgraph (c : constraints) := 
    foldr addC egraph c.

  Section ConstraintSyntax.

    Definition poly := (L * int)%type.
    Definition constr := (poly * poly)%type.
    Definition constrs := seq constr.
    Definition inst := L -> int.
    
    Definition substP (i : inst) (p : poly) := i p.1 + p.2.
    Definition substC (i : inst) (c : constr) : int * int :=
      (substP i c.1, substP i c.2).
    
    Definition validC (i : inst) (c : constr) := 
      let '(i, j) := substC i c in i <= j.
    
    Definition validCs (i : inst) (c : constrs) := 
      all (validC i) c.
    
    Definition constrs_to_graph (c : constrs) : graph := 
      foldr (fun c acc =>
               let '(p, q) := c in
               addC (p.1, p.2 - q.2, q.1) acc)
            egraph c.

  End ConstraintSyntax.

  Lemma constr_to_graph_fin (c : constrs) : finite (constrs_to_graph c).
  Proof.
    induction c.
    by exists [::]; move => x Hx.
    move: IHc a => [cl Hcl] [[l n] [l' n']].
    exists (l :: l' :: cl).
    move=> x; rewrite /= /upd add_merge in_cons.
    case: (x == l). 
      - by move=> /=.
      - rewrite // in_cons /= negb_or.
        move/andP => [H H']. now apply Hcl.
  Qed.

  Definition finite_measure (g : graph) (f : finite g) := 
    size (proj1_sig f).

  Definition graph_inst (g : graph) (fin : finite g) : node :=
    let dom := proj1_sig fin in
    if dom is x :: s then 
      (* Take random node *)
      if g x is Some a then 
        let empty _
      else (empty _)
    else
      (empty _).

    let start := [seq x <- dom | if g x is Some l then  && l 
      fun l => 
        if l \in dom then 
          let up := g l in
          

        .
    

  Lemma correctness (c : constrs) : 
    consistent (constrs_to_graph c) <-> exists i : inst, validCs i c.
  Proof. 
    split. 
    move=> Hc. 
  