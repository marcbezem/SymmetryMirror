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

File structure:
- Symmetry.v at the top documents the structure and exports all chapters;
  _CoqProject lists all files in dependency (= book) order.
- One directory per chapter (e.g. Circle/ for circle.tex), with a chapter
  file of the same name (Circle/Circle.v) that only re-exports its sections
  and starts with a summary of the whole chapter.
- One file per section, S<nn>_<Name>.v, with nn the book's section number.
  No file for overview sections, sections hidden in the book (\wip), or
  sections that are empty or still to be written.
- Each section file does Require Export of the previous section; the first
  section of a chapter exports the previous chapter file.
- Material the book repeats is formalized once, at its first occurrence;
  later sections refer to it.

Anchoring in the LaTeX source:
- The labels of the LaTeX source (\label{...}) are the anchor points of the
  formalization. The formalization of a labelled item (definition, lemma,
  exercise, example, remark, ...) is preceded by a comment naming the item
  and its label, e.g. (** Lemma [lem:ff-eso] ... *), and may consist of
  several Rocq items (auxiliary definitions and lemmas, variants).
  Labels are cited verbatim, exactly as in \label{...}, for searchability.
- Items without a label are anchored by a comment that names them by the
  nearest label (e.g. "the exercise after [def:mu_E]") or by their content.
- Items follow the order of the LaTeX source.

Contents of a section file:
- A header comment with the summary of the run: what is formalized (book
  labels and Rocq names), deviations from the text, NOTEs for the book
  text, and what is left out and why.
- A result that is left out is stated without proof at its anchor point,
  as Definition name_stmt : Type := ...; nothing is admitted. Results that
  cannot be stated formally (informal remarks, alternative proofs) are only
  listed in the summary.

Naming: use the book's names (from macros.tex). If a name clashes with an
earlier notion, add a suffix (e.g. isIsoC/IsoC for categories, since
isIso/Iso are the group isomorphisms).

Commit and push directly to main, one commit per section where possible.
