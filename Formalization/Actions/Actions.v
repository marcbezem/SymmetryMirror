(** * Chapter 5 of [actions.tex]: Actions

    ** Summary of this formalization

    Section 5.1 is an overview without results.  Sections 5.2 - 5.6:
    group actions ([S02_GSets.v]), subgroups ([S03_Subgroups.v]),
    invariant maps and orbits ([S04_Orbits.v]), torsors
    ([S05_Torsors.v]) and Cayley's theorem ([S06_Cayley.v]), one file
    per section,
    each starting with its own summary.  They build on Chapters 2 - 4 ([Group.Group]).
    Everything compiles with nothing admitted. *)

From SymmetryMirror Require Export
  Actions.S02_GSets
  Actions.S03_Subgroups
  Actions.S04_Orbits
  Actions.S05_Torsors
  Actions.S06_Cayley.
