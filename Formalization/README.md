This directory contains (experiments with) autoformalization.

Here are the instructions for Claude:

The Latex sources are at github.com/marcbezem/SymmetryMirror/*-tex.
Use rocq with the Coq-HoTT library.
All results should be uploaded to github.com/marcbezem/SymmetryMirror/Formalization.
Always build on earlier results in github.com/marcbezem/SymmetryMirror/Formalization.
Deviations from Book HoTT and the Coq-HoTT library include:
- path composition uses the same order as function composition
- pointing paths and fibers use y = f(x)

If a notion occurs definitionally in the Coq-Hott library, use it to define our notion,
such as: Definition book_name := library_name. Use book_name henceforth.
Include the summary that you write after each formalization run as a comment 
at the beginning of the .v file that you propose to commit and push.
