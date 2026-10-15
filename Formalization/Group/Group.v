(** * Chapter 4 of [group.tex]: Groups, concretely

    ** Summary of this formalization

    Section 4.1 is an overview without results.  Sections 4.2 - 4.3: the
    type of groups ([S02_TypeOfGroups.v]) and abstract groups
    ([S03_AbstractGroups.v]), one file per section, each starting
    with its own summary.  They build on Chapters 2 and 3
    ([Circle.Circle]).  Everything compiles with nothing admitted. *)

From SymmetryMirror Require Export
  Group.S02_TypeOfGroups
  Group.S03_AbstractGroups.
