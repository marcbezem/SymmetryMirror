(** * Chapter 3 of [circle.tex]: The universal symmetry: the circle

    ** Summary of this formalization

    Sections 3.1 - 3.3 of Chapter 3 of the book "Symmetry", one file per
    section, each starting with its own summary: the circle and its
    universal property ([S01_Circle.v]), the integers as a higher
    inductive type ([S02_Integers.v]) and coverings ([S03_Coverings.v]).
    They build on Chapter 2 ([IntroUF.IntroUF]).  Everything compiles with
    nothing admitted.

    The circle is the library's [Circle] and the integers are the
    library's [Pushout] of [-0] and [0] over [𝟙]; both are higher inductive
    types of Coq-HoTT (graph quotients).  [Funext] and [Univalence] are
    used only where needed. *)

From SymmetryMirror Require Export
  Circle.S01_Circle
  Circle.S02_Integers
  Circle.S03_Coverings.
