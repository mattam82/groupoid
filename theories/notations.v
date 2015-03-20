(** printing ~1 $\sim_1$ *)
(** printing ~2 $\sim_2$ *)
(** printing Π1 $\pi_1$*)
(** printing Π2 $\pi_2$*)
(** printing --> $\longrightarrow$*)
(** printing ---> $\longrightarrow$*)
(** printing β $\beta$*)
(** printing [! $\llbracket$*)
(** printing !] $\rrbracket$*)
(** printing |- $\vdash$*)
(** printing === $\equiv$*)
(** We use the following notations throughout: Sigma type introduction
  is written [(t ; p)] when its predicate/fibration is inferrable from
  the context, and projections are denoted [Π1] and [Π2]. The bracket
  notation [[_]] is an alias for [Π1]. The following is directly
  extracted from Coq files using the <<coqdoc>> tool (source files
  are available at %\url{http://mattam82.github.io/groupoid}%). If
  you are reading the colored version of the paper, keywords are
  typeset in red, inductive types and classes in blue, inductive
  constructors in dark red, and constants and lemmas in green.
  *)
(* begin hide *)
Notation Π1 := projT1.
Notation Π2 := projT2.
Notation " ( x ; p ) " := (existT _ x p).
(* end hide *)
