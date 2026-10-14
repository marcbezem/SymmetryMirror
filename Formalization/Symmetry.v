(** * Formalization of the book "Symmetry"

    Rocq with the Coq-HoTT library; the LaTeX sources are the files
    [*.tex] in the parent directory.  Build with [coqc -noinit
    -indices-matter] (see [_CoqProject]).

    ** Structure

    - [Symmetry.v] (this file) exports all chapters.
    - One directory per chapter, with a chapter file that exports its
      sections: [IntroUF/IntroUF.v] (Chapter 2, [intro-uf.tex]) and
      [Circle/Circle.v] (Chapter 3, [circle.tex], Sections 3.1 - 3.9).
    - One file per section, [S<nn>_<Name>.v], each starting with a summary
      of what is formalized, what differs from the text, and NOTEs for the
      book text.  Each section exports the previous one, and the first
      section of a chapter exports the previous chapter.

    ** Conventions

    The book deviates from Book HoTT and the Coq-HoTT library:
    1. Path composition is written in the order of function composition:
       for [p : a = b] and [q : b = c] we write [q ⋅ p :≡ trans p q], with
       [trans] defined by induction on [q] as in the book.
    2. Pointing paths and fibers use [y = f(x)]:
       [f⁻¹(y) :≡ ∑_x (y = f(x))].
    3. The book's [happly] is called [ptw], for dependent functions.

    When a notion occurs definitionally in Coq-HoTT, i.e. the library's
    definition satisfies the book's defining equations by definition, we
    define the book's notion from it ([Definition book_name :=
    library_name]) and use the book's name henceforth.  Constructors
    ([refl], [yes], [no], [triv]) are renamed by notations, so that they
    can still be used in patterns.  Where the book uses judgmental
    equality [≡], we check it by [refl]. *)

From SymmetryMirror Require Export
  IntroUF.IntroUF
  Circle.Circle.
