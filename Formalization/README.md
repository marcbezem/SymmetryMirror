This directory contains (experiments with) autoformalization.

Here are the instructions for Claude:

The Latex sources are at github.com/marcbezem/SymmetryMirror/*-tex
Use rocq with the Coq-HoTT library.
All results should be uploaded to github.com/marcbezem/SymmetryMirror/Formalization by PRs
Always build on earlier results in github.com/marcbezem/SymmetryMirror/Formalization
Deviations from Book HoTT include:
- path composition uses the same order as function composition
- pointing paths and fibers use y = f(x)
- the function happly is called ptw and is also defined for dependent functions
If a notion is already present in the Coq-Hott library, use it to define our notion, such as ptw.
Do not redefine notions such as you did in your first attempt with the natural numbers.
Include the summary that you write after each formalization run as a comment 
at the beginning of the .v file that you propose to commit and push.
