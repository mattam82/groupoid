(** printing elU1 $\cstu{\textnormal{\coqdocdefinition{U1}}}{}$ *)
(** printing elU2 $\cstu{\textnormal{\coqdocdefinition{U2}}}{}$ *)
(** printing elU2u $\cstu{\textnormal{\coqdocdefinition{U2}}}{u}$ *)
(** printing elU2u' $\cstu{\textnormal{\coqdocdefinition{U2}}}{u'}$ *)
(** printing Typeu $\textnormal{\coqdockw{Type}}_{u}$ *)
(** printing Typeu' $\textnormal{\coqdockw{Type}}_{u'}$ *)
(** printing Typev $\textnormal{\coqdockw{Type}}_{v}$ *)
(** printing Typeu1 $\textnormal{\coqdockw{Type}}_{u+1}$ *)

Definition U2 := Type.
Definition U1 := Type : U2.

(**

In the non-polymorphic case but with typical ambiguity, these two
definitions are elaborated as [elU2 := Typeu : Typeu1] and 
[elU1 := Typev : elU2] with a single, global constraint $v < u$.

In a polymorphic setting, [U2] is elaborated as a polymorphic
constant [elU2u := Typeu : Typeu1] where $u$ is
a bound universe variable. The monomorphic definition of [U1]
is elaborated as [elU1 := Typev : elU2u'] $\equiv$ [Typeu'] with a single global
constraint $v < u'$ for a fresh $u'$. In other words, [U2]'s
universe is no longer fixed and a fresh level is generated at every
occurrence of the constant.


*)