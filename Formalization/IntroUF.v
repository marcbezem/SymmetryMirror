(** * Formalization of Chapter 2 of [intro-uf.tex]

    Chapter 2, "An introduction to univalent mathematics", of the book
    "Symmetry", Sections 2.2 - 2.27, in Rocq with the Coq-HoTT library.

    ** Summary of this formalization

    This file is the concatenation of eight parts, formalized in
    successive runs and originally kept in separate files [IntroUF.v],
    [IntroUF2.v], ..., [IntroUF8.v]; each part starts with the summary
    written for it.  The file compiles with
    [coqc -noinit -indices-matter], with nothing admitted.

    - Part 1: Sections 2.2 - 2.6     - Part 5: Sections 2.19 - 2.21
    - Part 2: Sections 2.7 - 2.12    - Part 6: Section 2.22
    - Part 3: Sections 2.13 - 2.15   - Part 7: Sections 2.23 - 2.24
    - Part 4: Sections 2.16 - 2.18   - Part 8: Sections 2.25 - 2.27

    In the part summaries, "this file" refers to the part, and
    [IntroUFi.v] to part [i] (with [IntroUF.v] for part 1).  The bridges
    to Coq-HoTT notions that are used from 2.16 on ([Eqv_of_props],
    [fiber_hfiber], [isSet_IsHSet], [IsHSet_isSet], [Equiv_of_Eqv]) are at
    the end of part 3; all other bridges are in [Bridge.v], which imports
    this file.  Changes made when concatenating: the constructor of the
    negated naturals [NNN] is renamed [negN] (it clashed with negation
    [neg]), and the proof of [pEqv_total_isContr] destructs its arguments
    before [refl] (the original version became very slow to check).

    Deviations from Book HoTT and the Coq-HoTT library: path composition
    uses the order of function composition ([q ⋅ p :≡ trans p q]),
    pointing paths and fibers use [y = f(x)], and [happly] is called
    [ptw] (for dependent functions).  Notions that occur definitionally
    in Coq-HoTT are defined as [Definition book_name := library_name] and
    used under the book's name. *)

From HoTT Require Import
  Basics Types.Sigma Types.Equiv Types.Bool Types.Universe Types.Forall
  Cubical.DPath Truncations.Core Truncations.SeparatedTrunc
  Universes.TruncType Colimits.Quotient Spaces.Nat.Core
  Spaces.Nat.Factorial Spaces.Nat.Division Spaces.Finite.Fin
  Spaces.Finite.FinNat Spaces.Finite.Finite Spaces.List.Core.

Declare Scope uf_scope.
Delimit Scope uf_scope with uf.
Local Open Scope uf_scope.

(** * Part 1: Sections 2.2 - 2.6

    Chapter 2, "An introduction to univalent mathematics", of the book
    "Symmetry".  We use Rocq with the Coq-HoTT library.

    ** Summary of this formalization

    Sections 2.2 - 2.6 are formalized in this file.  It compiles with
    [coqc -noinit -indices-matter] against Coq-HoTT and uses no axioms:
    [Print Assumptions] reports "Closed under the global context" for the
    results checked.  The only place function extensionality appears is
    the funext remark in 2.6, which assumes Coq-HoTT's [Funext] but is
    never used.

    Book notions defined from Coq-HoTT notions that satisfy the book's
    defining equations by definition: [cst := const], [comp := Compose]
    (notation [g ∘ f]), [id := idmap], [ℕ := nat], [succ := S],
    [ind_ℕ := nat_ind], [iter] from [nat_iter], addition [add n m :=
    nat_add m n] (the book recurses on the second argument, the library
    on the first), [mul := nat_mul], [fact := factorial],
    [path_ind := paths_ind], [symm := inverse], [trp := transport] and
    [ptw := apD10]; [ap] has the same name in the book and the library,
    and [refl] is a notation for the constructor [idpath].

    Own definitions: [trans], which the book defines by induction on the
    second argument, so that [p ∙ refl ≡ p]; the library's [concat]
    recurses on both arguments.  Hence also the path-groupoid laws, path
    powers and the naturality square [ns] are proved for [trans].

    What's covered, by section
    - 2.2: [cst], composition, [id], and associativity and both unit laws
      holding by definition.
    - 2.3: the universe hierarchy and cumulativity, and the
      correspondence between families of types and functions into a
      universe.
    - 2.4: rule (P4) as [ind_ℕ], with both computation rules holding by
      definition; recursion, iteration, [add], [mul] and [fact], whose
      defining equations all hold by definition, as do [2+2 ≡ 4] and
      [fact 3 ≡ 6].  The alternative definitions via iteration are even
      equal by definition to [add] and [mul].
    - 2.5: rule (E3) as [path_ind], plus [symm], [trans] and all six parts
      of the path-groupoid-laws exercise; powers [p ^^ n] with
      [p^(n+1) :≡ p · p^n], and negative powers; [trp] and both transport
      exercises, proved by path induction without funext; the transport
      of structure example for [T(x) :≡ (x = x)], with the added fact
      (not stated in the text) that this transport is conjugation.
    - 2.6: [ap]; all three parts of [lem:apcomp]; the exercise
      [xca:trp-ap]; [ptw] and its identification with the footnote's
      [ap (ev x)]; the funext remark (via [path_forall]); the naturality
      square [ns(h,p)].

    Things that differ from the text
    - The informal examples about reals and polygons are left out.
    - Coq-HoTT reserves [⋅] without associativity, so iterated
      compositions need parentheses.
    - Numerals need [%nat], because they otherwise default to the
      library's truncation levels; [+] and [·] are written [add], [mul].

    ** Conventions

    The book deviates from Book HoTT and the Coq-HoTT library:
    1. Path composition is written in the same order as function
       composition: for [p : a = b] and [q : b = c] the book writes
       [p ∙ q], or [q · p], or [q ∘ p].  We define [trans p q] following
       the book (by induction on [q]) and use the notation [q ⋅ p].
    2. Pointing paths and fibers use [y = f x].

    When a notion occurs definitionally in Coq-HoTT, that is, when the
    library's definition satisfies the book's defining equations by
    definition, we define the book's notion from it, as in
    [Definition book_name := library_name], and use the book's name
    henceforth.  Constructors ([refl], [yes], [no], [triv], ...) are
    renamed by notations instead, so that they can still be used in
    patterns.

    Book notation [a ⥲ b] (the identity type) is HoTT's [a = b].  Where
    the book uses judgmental equality [≡], we verify it by type checking
    [refl] (i.e., by conversion). *)

(** [refl a] is the constructor [idpath a] of the identity type. *)
Notation refl := idpath.

(** ** 2.2 Types, elements, families, and functions *)

(** A family of types [T(x)] parametrized by [x : X] is a function
    [X -> Type]; a family of elements [e(x) : T(x)] is a dependent
    function, an element of the product type [forall x : X, T x],
    the book's [∏_{x:X} T(x)].  If [T] is constant this is the function
    type [X -> T]. *)

(** Definition [def:cst-map]: the constant function at [t]. *)
Definition cst {X T : Type} : T -> X -> T := @const X T.

(** Composition of functions: [g ∘ f :≡ (a ↦ g(f(a)))]. *)
Definition comp {X Y Z : Type} : (Y -> Z) -> (X -> Y) -> X -> Z
  := @Compose X Y Z.

Notation "g ∘ f" := (comp g f) : uf_scope.

(** The identity function [id_X :≡ (a ↦ a)]. *)
Definition id (X : Type) : X -> X := idmap.

Section TypesElementsFamiliesFunctions.

  Context {X Y Z W : Type} (f : X -> Y) (g : Y -> Z) (h : Z -> W).

  Definition comp_def : g ∘ f = (fun a => g (f a)) := refl.

  (** Associativity holds by definition: [(h ∘ g) ∘ f ≡ h ∘ (g ∘ f)]. *)
  Definition comp_assoc_jdeq : (h ∘ g) ∘ f = h ∘ (g ∘ f) := refl.

  (** Unit laws hold by definition, using the eta rule
      [f ≡ (a ↦ f(a))]. *)
  Definition comp_id_r_jdeq : f ∘ id X = f := refl.
  Definition comp_id_l_jdeq : id Y ∘ f = f := refl.

End TypesElementsFamiliesFunctions.

(** ** 2.3 Universes

    Coq-HoTT has a hierarchy of universes [Type@{i}], which is
    cumulative: if [i < j] and [X : Type@{i}] then [X : Type@{j}].
    The smallest universe [U_0] is [Type0] in Coq-HoTT, which contains
    the basic types [ℕ], [False], [True], ... *)

Section Universes.

  Universes i j.
  Constraint i < j.

  (** Every universe is an element of a larger one. *)
  Definition universe_in_larger : Type@{j} := Type@{i}.

  (** Cumulativity (item [it:cumulative]). *)
  Definition cumulative (X : Type@{i}) : Type@{j} := X.

  (** Correspondence between families of types and functions into a
      universe: a family [T(x)] with [T(x) : U] gives [x ↦ T(x) : X -> U],
      and conversely [f' : X -> U] gives the family [f'(x)].  In Rocq
      these two views coincide: a family of types simply *is* a function
      into a universe. *)
  Definition family_to_function {X : Type@{i}} (T : X -> Type@{i})
    : X -> Type@{i} := fun x => T x.

  Definition family_to_function_eta {X : Type@{i}} (T : X -> Type@{i})
    : family_to_function T = T := refl.

  (** Function types between types in [U] are again in [U]. *)
  Definition fun_type_in_U (X Y : Type@{i}) : Type@{i} := X -> Y.

End Universes.

(** ** 2.4 The type of natural numbers

    Rules (P1) - (P3): [ℕ : U_0], [0 : ℕ], [succ : ℕ -> ℕ]. *)

Definition ℕ : Type0 := nat.
Bind Scope nat_scope with ℕ.

Definition succ : ℕ -> ℕ := S.

(** Rule (P4): induction on ℕ, with its two computation rules holding by
    definition. *)
Definition ind_ℕ (X : ℕ -> Type) (a : X 0%nat)
  (g : forall m, X m -> X (succ m)) : forall m, X m
  := nat_ind X a g.

Definition ind_ℕ_0 X a g : ind_ℕ X a g 0%nat = a := refl.
Definition ind_ℕ_succ X a g m
  : ind_ℕ X a g (succ m) = g m (ind_ℕ X a g m) := refl.

(** The recursion principle is the special case of a constant family. *)
Definition rec_ℕ (Y : Type) (a : Y) (g : ℕ -> Y -> Y) : ℕ -> Y
  := ind_ℕ (fun _ => Y) a g.

(** Iteration: [e^0 :≡ id_Y] and [e^(succ m) :≡ e ∘ e^m]. *)
Definition iter {Y : Type} (e : Y -> Y) (m : ℕ) : Y -> Y
  := fun y => nat_iter m e y.

Definition iter_0 {Y : Type} (e : Y -> Y) : iter e 0%nat = id Y := refl.
Definition iter_succ {Y : Type} (e : Y -> Y) m
  : iter e (succ m) = e ∘ iter e m := refl.

(** Addition, by induction on the second argument:
    [n + 0 :≡ n] and [n + succ(m) :≡ succ(n + m)].  This is the library's
    [nat_add] with its arguments swapped. *)
Definition add (n m : ℕ) : ℕ := nat_add m n.

(** Multiplication, by induction on the first argument:
    [0 · n :≡ 0] and [succ(m) · n :≡ (m · n) + n]. *)
Definition mul (m n : ℕ) : ℕ := nat_mul m n.

(** The factorial function:
    [fact(0) :≡ 1] and [fact(succ(m)) :≡ succ(m) · fact(m)]. *)
Definition fact : ℕ -> ℕ := factorial.

Section NaturalNumbers.

  Local Open Scope nat_scope.

  Definition add_0 (n : ℕ) : add n 0 = n := refl.
  Definition add_succ (n m : ℕ) : add n (succ m) = succ (add n m) := refl.

  Definition mul_0 (n : ℕ) : mul 0 n = 0 := refl.
  Definition mul_succ (m n : ℕ) : mul (succ m) n = add (mul m n) n := refl.

  Definition fact_0 : fact 0 = 1 := refl.
  Definition fact_succ (m : ℕ) : fact (succ m) = mul (succ m) (fact m) := refl.

  Definition two_plus_two : add 2 2 = 4 := refl.
  Definition fact_3 : fact 3 = 6 := refl.

  (** Examples from 2.2: [m ↦ (n ↦ m + n)] and [2 + _]. *)
  Check (fun m => (fun n => add m n)) : ℕ -> (ℕ -> ℕ).
  Check (fun n => add 2 n) : ℕ -> ℕ.

  (** Alternative definitions via iteration, [n + m :≡ succ^m(n)] and
      [m · n :≡ (i ↦ i + n)^m(0)], are equal by definition to the ones
      above. *)
  Definition add_iter (n m : ℕ) : add n m = iter succ m n := refl.
  Definition mul_iter (m n : ℕ) : mul m n = iter (fun i => add i n) m 0
    := refl.

End NaturalNumbers.

(** ** 2.5 Identity types

    Rules (E1) - (E3).  (E1) is the identity type [a = b] (HoTT's
    [paths], which lives in the same universe as [X]); (E2) is
    [refl a : a = a]; (E3) is based path induction, with its computation
    rule holding by definition.  Possible further parameters of [P] can
    be absorbed into [P]. *)

Definition path_ind {X : Type} (a : X) (P : forall b : X, a = b -> Type)
  (p : P a refl) : forall (b : X) (e : a = b), P b e
  := paths_ind a P p.

Definition path_ind_refl {X : Type} (a : X) P p
  : path_ind a P p a refl = p := refl.

(** Example: [refl_2 : fact(2) = 2]. *)
Definition fact_2 : fact 2%nat = 2%nat := refl 2%nat.

(** Definition [def:eq-symm]: path inverse, [symm_{a,a}(refl a) :≡ refl a]. *)
Definition symm {X : Type} {a b : X} (p : a = b) : b = a := inverse p.

Notation "p ⁻¹" := (symm p) : uf_scope.

Definition symm_refl {X : Type} (a : X) : (refl a)⁻¹ = refl a := refl.

(** Definition [def:eq-trans]: path composition, defined by induction on
    the second argument: [trans_{a,b,b}(p)(refl b) :≡ p].  The library's
    [concat] is defined by induction on both arguments, so it does not
    satisfy this equation by definition. *)
Definition trans {X : Type} {a b c : X} (p : a = b) (q : b = c) : a = c
  := match q with refl => p end.

(** Notation in the order of function composition: [q ⋅ p :≡ p ∙ q]. *)
Notation "q ⋅ p" := (trans p q) : uf_scope.

Definition trans_refl_jdeq {X : Type} {a b : X} (p : a = b)
  : refl ⋅ p = p := refl.

(** Comparison with the library. *)
Definition trans_is_concat {X : Type} {a b c : X} (p : a = b) (q : b = c)
  : q ⋅ p = p @ q.
Proof. destruct q, p. exact refl. Defined.

(** Exercise [xca:path-groupoid-laws]. *)
Section PathGroupoidLaws.

  Context {X : Type} {a b c d : X}.

  (** 1. [p ∙ refl_b = p] (holds by definition). *)
  Definition trans_p1 (p : a = b) : refl ⋅ p = p := refl.

  (** 2. [refl_a ∙ p = p]. *)
  Definition trans_1p (p : a = b) : p ⋅ refl = p
    := match p with refl => refl end.

  (** 3. [(p ∙ q) ∙ r = p ∙ (q ∙ r)]. *)
  Definition trans_assoc (p : a = b) (q : b = c) (r : c = d)
    : r ⋅ (q ⋅ p) = (r ⋅ q) ⋅ p
    := match r with refl => refl end.

  (** 4. [p⁻¹ ∙ p = refl_b]. *)
  Definition trans_Vp (p : a = b) : p ⋅ p⁻¹ = refl
    := match p with refl => refl end.

  (** 5. [p ∙ p⁻¹ = refl_a]. *)
  Definition trans_pV (p : a = b) : p⁻¹ ⋅ p = refl
    := match p with refl => refl end.

  (** 6. [(p⁻¹)⁻¹ = p]. *)
  Definition symm_symm (p : a = b) : (p⁻¹)⁻¹ = p
    := match p with refl => refl end.

End PathGroupoidLaws.

(** Powers of a symmetry [p : a = a]: [p^0 :≡ refl_a] and
    [p^(n+1) :≡ p · p^n]; negative powers [p^(-n) :≡ (p⁻¹)^n]. *)
Fixpoint path_pow {X : Type} {a : X} (p : a = a) (n : ℕ) : a = a
  := match n with
     | O => refl
     | S n' => p ⋅ path_pow p n'
     end.

Notation "p ^^ n" := (path_pow p n) (at level 30) : uf_scope.

Definition path_pow_neg {X : Type} {a : X} (p : a = a) (n : ℕ) : a = a
  := (p⁻¹) ^^ n.

(** Definition [def:transport]: [trp^T_{refl a} :≡ id_{T(a)}]. *)
Definition trp {X : Type} (T : X -> Type) {a b : X} (e : a = b)
  : T a -> T b
  := transport T e.

Definition trp_refl {X : Type} (T : X -> Type) (a : X)
  : trp T (refl a) = id (T a) := refl.

(** Exercise [xca:trp-compose]: [trp_{e' ∘ e} = trp_{e'} ∘ trp_e].
    This is an identification of functions; no function extensionality
    is needed, since after induction on [e'] both sides are [trp_e]
    by definition. *)
Definition trp_compose {X : Type} (T : X -> Type) {a b c : X}
  (e : a = b) (e' : b = c)
  : trp T (e' ⋅ e) = trp T e' ∘ trp T e
  := match e' with refl => refl end.

(** Exercise [xca:trp-nondep]: in a constant family [trp^Y_p = id_Y]. *)
Definition trp_const {X Y : Type} {a b : X} (p : a = b)
  : trp (fun _ => Y) p = id Y
  := match p with refl => refl end.

(** Example: transport of structure in [T(x) :≡ (x = x)], which transports
    a symmetry of [a] to a symmetry of [b]. *)
Definition trp_symmetry {X : Type} {a b : X} (e : a = b)
  : (a = a) -> (b = b)
  := trp (fun x => x = x) e.

(** By induction, this is conjugation: [trp_e(s) = e · s · e⁻¹]. *)
Definition trp_symmetry_conj {X : Type} {a b : X} (e : a = b) (s : a = a)
  : trp_symmetry e s = (e ⋅ s) ⋅ e⁻¹
  := match e with refl => (trans_1p s)⁻¹ end.

(** ** 2.6 Product types

    If [X : U] and [Y : X -> U] then [forall x, Y x : U]. *)

Definition pi_in_U@{u} (X : Type@{u}) (Y : X -> Type@{u}) : Type@{u}
  := forall x : X, Y x.

(** Definition [def:ap]: [ap_{f,x,x}(refl x) :≡ refl_{f(x)}].  This is
    the library's [ap], which has the same name. *)
Definition ap_refl {X Y : Type} (f : X -> Y) (x : X)
  : ap f (refl x) = refl (f x) := refl.

(** Construction [lem:apcomp]. *)
Section ApComp.

  Context {X Y : Type} (f : X -> Y) {x x' x'' : X}.

  Definition ap_trans (p : x = x') (p' : x' = x'')
    : ap f (p' ⋅ p) = ap f p' ⋅ ap f p.
  Proof. destruct p', p. exact refl. Defined.

  Definition ap_symm (p : x = x') : ap f (p⁻¹) = (ap f p)⁻¹
    := match p with refl => refl end.

  Definition ap_id (p : x = x') : ap (id X) p = p
    := match p with refl => refl end.

End ApComp.

(** Exercise [xca:trp-ap]: [trp^{T ∘ f}_p = trp^T_{ap_f(p)}], both of type
    [T(f(a)) -> T(f(a'))]. *)
Definition trp_ap {X A : Type} (T : X -> Type) (f : A -> X)
  {a a' : A} (p : a = a')
  : trp (T ∘ f) p = trp T (ap f p)
  := match p with refl => refl end.

(** Definition [def:ptw]: from an identification of (dependent) functions
    to pointwise identifications, [ptw_{f,f}(refl f) :≡ x ↦ refl_{f(x)}].
    This is the library's [apD10] (Book HoTT's [happly]). *)
Definition ptw {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) : forall x : X, f x = g x
  := apD10 p.

Definition ptw_refl {X : Type} {Y : X -> Type} (f : forall x, Y x)
  : ptw (refl f) = (fun x => refl (f x)) := refl.

(** Footnote to [def:ptw]: the alternative via evaluation
    [ev_x(f) :≡ f(x)].  Not equal by definition, but identified. *)
Definition ev {X : Type} {Y : X -> Type} (x : X) : (forall x, Y x) -> Y x
  := fun f => f x.

Definition ptw_ev {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) (x : X) : ptw p x = ap (ev x) p
  := match p with refl => refl end.

(** Function extensionality ([def:funext], postulated later in the book)
    provides the converse; in Coq-HoTT it is the class [Funext], with
    [path_forall : (forall x, f x = g x) -> f = g]. *)
Definition funext_converse `{Funext} {X : Type} {Y : X -> Type}
  {f g : forall x, Y x} : (forall x, f x = g x) -> f = g
  := path_forall f g.

(** Definition [def:naturality-square]: for [h : ∏_x f(x) = g(x)] and
    [p : x = x'], an identification
    [ns(h,p) : h(x') · ap_f(p) = ap_g(p) · h(x)].
    For [p :≡ refl_x] the goal is [h(x) · refl_{f(x)} = h(x)], which is
    constructed by induction on [h(x)] (exercise part 2). *)
Definition ns {X Y : Type} {f g : X -> Y} (h : forall x, f x = g x)
  {x x' : X} (p : x = x')
  : h x' ⋅ ap f p = ap g p ⋅ h x
  := match p with refl => trans_1p (h x) end.

(** * Part 2: Sections 2.7 - 2.12

    ** Summary of this formalization

    Sections 2.7 - 2.12 are formalized in this file, which builds on
    [IntroUF.v].  It compiles cleanly.  [Print Assumptions] shows that
    only the function-extensionality results depend on Coq-HoTT's
    [Funext] axiom; the other results checked use no axioms.

    Book notions defined from Coq-HoTT notions that satisfy the book's
    defining equations by definition: [PathOver := DPath] (so that
    [po_p] holds by definition), [po_inv := dp_inverse], [apd := apD],
    [apap := ap011D], [fst := pr1], [snd := pr2], [pair := exist],
    [tot := functor_sigma idmap], [False := Empty], [True := Unit] (with
    [triv], [yes], [no] as notations for constructors), lists [X^*] with
    [list_ind], [len := length] and concatenation [app].

    Own definitions, because the library's notion differs:
    - composition of paths over paths [⊙], over the book's [trans];
    - [isContr X :≡ Σ c, ∏ x, (c = x)] (the library's [Contr] is a
      different inductive definition);
    - [fiber f y := Σ x, (y = f x)], with the book's convention, hence
      [isEquiv f := ∏ y, isContr (fiber f y)] and the type [X ≃ Y];
    - the pair-path map [pair⁼(p,q) :≡ apap pair p q] and its inverse;
    - the binary product [X × Y :≡ Σ_{x:X} Y] (not the library's [prod],
      to which it is shown equivalent);
    - [ptw⁻¹], the inverse given by [funext : isEquiv ptw];
    - unary sums [Copy], the negated naturals [NNN], and [hd], [tl] with
      values in [X ⨿ True] (the library's [head] uses [option]); [rev] is
      defined from concatenation (the library's [reverse] uses an
      accumulator).

    Where the book cites the HoTT Book for a proof (the converse of
    [lem:weq-iso], and [lem:fiberwise-equiv-from-tot], Thm 4.7.7) we use
    Coq-HoTT's [isequiv_adjointify] and [isequiv_from_functor_sigma], via
    conversions in both directions between [isEquiv] and [IsEquiv].
    Function extensionality is the book's principle [funext], obtained
    from Coq-HoTT's axiom [isequiv_apD10].

    Remarks
    - Sum types have definitional η, so AC-in-TT, currying,
      Σ-associativity, Σ-commutation and Σ-distributivity are
      equivalences whose round trips hold by definition.
    - Exercise [xca:cp]: four laws for paths over paths (left unit, right
      unit, inverse, double inverse), stated by transporting along the
      corresponding laws for paths where needed.
    - [snd(pair⁼(p,q)) = q]: taken literally, the two sides have
      different types.  It is stated together with the [fst] part as
      [Ψ(pair⁼(p,q)) = (p,q)], where [Ψ] is the inverse map.
    - [lem:isEq-pair-bin=]: [q : y = y'] isn't definitionally a path over
      [p], so the map converts [q] with [po_const].
    - Exercise [xca:binary-sum-id]: the encode–decode method is used
      rather than the route the book suggests.
    - Exercise [xca:sum-equiv-base] uses Coq-HoTT's
      [equiv_functor_sigma_pb], because a direct proof needs half-adjoint
      coherence, which the book hasn't introduced yet.
    - The footnote's alternative proof of contract-away is left out.
    - A file that imports this one should import [HoTT.Basics] first, or
      Rocq reports a notation-level conflict.

    ** Conventions

    Continuation of [IntroUF.v]; the same conventions apply:
    1. path composition in function-composition order, [q ⋅ p :≡ p ∙ q],
       with [trans] defined by induction on the second argument;
    2. fibers are defined using [y = f x]: [f⁻¹(y) :≡ ∑_{x:X} (y = f x)];
    3. notions that occur definitionally in Coq-HoTT are defined from
       the library notion and used under the book's name.

    Sum types are Coq-HoTT's [sig], written [{x : X & Y x}], with pairs
    [(x; y)]; the book's projections [fst] and [snd] are defined from the
    library's [fst] and [snd].  The record [sig] has primitive
    projections, hence definitional eta, which makes many round trips
    below hold by definition.

    Where the book refers to the HoTT Book for a proof (the converse of
    [lem:weq-iso], and [lem:fiberwise-equiv-from-tot]), we use the
    corresponding results of Coq-HoTT, via a bridge between the book's
    [isEquiv] and Coq-HoTT's [IsEquiv]. *)

(** The finite types of 2.12, used throughout: [False] (the book's [∅]),
    [True] with its element [triv], and [Bool] with [yes] and [no]. *)
Definition False : Type0 := Empty.
Definition True : Type0 := Unit.
Notation triv := tt.
Notation yes := true.
Notation no := false.

(** ** 2.7 Identifying elements in members of families of types *)

(** Definition [def:pathsoverpaths]: the type [y =^Y_p y'] of paths from
    [y] to [y'] over [p].  The book defines it by induction on [p], with
    [y =^Y_{refl a} y' :≡ (y = y')]; the library's [DPath Y p y y'],
    defined as [transport Y p y = y'], satisfies this by definition. *)
Definition PathOver {X : Type} (Y : X -> Type) {a a' : X} (p : a = a')
  : Y a -> Y a' -> Type
  := DPath Y p.

Definition PathOver_refl {X : Type} (Y : X -> Type) {a : X} (y y' : Y a)
  : PathOver Y refl y y' = (y = y') := refl.

(** Remark: for a constant family the types of paths over [p] and of
    paths can be identified, by induction on [p].  (This is an
    identification of types, no univalence is needed.) *)
Definition PathOver_const {X Z : Type} {a a' : X} (p : a = a') (z z' : Z)
  : PathOver (fun _ => Z) p z z' = (z = z').
Proof. destruct p. exact refl. Defined.

(** Definition [def:pathover-trp]: [po_p : (y =^Y_p y') = (trp^Y_p(y) = y')],
    which holds by definition since paths over paths are [DPath]s. *)
Definition po {X : Type} {Y : X -> Type} {a a' : X} (p : a = a')
  (y : Y a) (y' : Y a') : PathOver Y p y y' = (trp Y p y = y')
  := refl.

(** Definition [def:pathovercomposition]: composition of paths over paths,
    by induction on [p'] and then on [q']. *)
Definition po_comp {X : Type} {Y : X -> Type} {x x' x'' : X}
  {p : x = x'} {p' : x' = x''} {y : Y x} {y' : Y x'} {y'' : Y x''}
  (q' : PathOver Y p' y' y'') (q : PathOver Y p y y')
  : PathOver Y (p' ⋅ p) y y''.
Proof. destruct p'. cbn in q'. destruct q'. exact q. Defined.

Notation "q' ⊙ q" := (po_comp q' q) (at level 40, left associativity) : uf_scope.

(** The inverse of a path over a path: the library's [dp_inverse]. *)
Definition po_inv {X : Type} {Y : X -> Type} {x x' : X} {p : x = x'}
  {y : Y x} {y' : Y x'} (q : PathOver Y p y y') : PathOver Y p⁻¹ y' y
  := dp_inverse q.

(** Exercise [xca:cp]: some groupoid laws for paths over paths.  Where the
    paths underneath are not equal by definition, we transport along the
    corresponding law from [xca:path-groupoid-laws]. *)
Section PathOverLaws.

  Context {X : Type} {Y : X -> Type} {x x' : X} {p : x = x'}
    {y : Y x} {y' : Y x'} (q : PathOver Y p y y').

  Definition po_comp_1q : (refl : PathOver Y refl y' y') ⊙ q = q
    := refl.

  Definition po_comp_q1
    : trp (fun r => PathOver Y r y y') (trans_1p p)
        (q ⊙ (refl : PathOver Y refl y y)) = q.
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

  Definition po_comp_Vq
    : trp (fun r => PathOver Y r y y) (trans_pV p) (po_inv q ⊙ q) = refl.
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

  Definition po_inv_inv
    : trp (fun r => PathOver Y r y y') (symm_symm p) (po_inv (po_inv q)) = q.
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

End PathOverLaws.

(** Definition [def:apd]: dependent application of [f] to paths,
    [apd_f(refl x) :≡ refl_{f(x)}]: the library's [apD]. *)
Definition apd {X : Type} {Y : X -> Type} (f : forall x, Y x)
  {x x' : X} (p : x = x') : PathOver Y p (f x) (f x')
  := apD f p.

Definition apd_refl {X : Type} {Y : X -> Type} (f : forall x, Y x) (x : X)
  : apd f (refl x) = refl := refl.

(** Definition [def:applfun2]: application of a function of two variables
    to a path and a path over it, [apap_g(refl x)(refl y) :≡ refl]: the
    library's [ap011D]. *)
Definition apap {X Z : Type} {Y : X -> Type} (g : forall x, Y x -> Z)
  {x x' : X} {y : Y x} {y' : Y x'} (p : x = x') (q : PathOver Y p y y')
  : g x y = g x' y'
  := ap011D g p q.

(** Definition [def:applfun2comp]. *)
Definition apap_refl {X Z : Type} {Y : X -> Type} (g : forall x, Y x -> Z)
  {x : X} {y y' : Y x} (q : y = y')
  : apap g refl q = ap (g x) q
  := match q with refl => refl end.

(** ** 2.8 Sum types

    The sum type [∑_{x:X} Y(x)] is [{x : X & Y x}], also denoted [Tot(Y)].
    If [X] and [Y(x)] are in [U], then so is the sum. *)

Notation Tot Y := (sig Y).

Definition sum_in_U@{u} (X : Type@{u}) (Y : X -> Type@{u}) : Type@{u}
  := {x : X & Y x}.

(** First and second projection: [fst(a,b) :≡ a] and [snd(a,b) :≡ b],
    the library's [fst] and [snd]. *)
Definition fst {X : Type} {Y : X -> Type} (z : {x : X & Y x}) : X := pr1 z.
Definition snd {X : Type} {Y : X -> Type} (z : {x : X & Y x}) : Y (fst z)
  := pr2 z.

Definition fst_jdeq {X : Type} {Y : X -> Type} (a : X) (b : Y a)
  : fst (a; b) = a := refl.
Definition snd_jdeq {X : Type} {Y : X -> Type} (a : X) (b : Y a)
  : snd (a; b) = b := refl.

Check (@snd : forall {X : Type} {Y : X -> Type} (z : {x : X & Y x}), Y (fst z)).

(** Remark [rem:non-dependent-sums]: the binary product [X × Y] is the sum
    over a constant family (see 2.11).  Remark [rem:iterated-sums]:
    [(x, y, z) :≡ (x, (y, z))]. *)
Definition triple {X : Type} {Y : X -> Type} {Z : forall x, Y x -> Type}
  (x : X) (y : Y x) (z : Z x y) : {x : X & {y : Y x & Z x y}}
  := (x; y; z).

(** ** 2.9 Equivalences *)

(** Definition [def:contractible]. *)
Definition isContr (X : Type) : Type := {c : X & forall x : X, c = x}.

(** Any element of a contractible type can serve as the center. *)
Definition isContr_center {X : Type} (H : isContr X) (a : X)
  : forall x : X, a = x
  := fun x => snd H x ⋅ (snd H a)⁻¹.

(** Lemma [lem:thepathspaceiscontractible]: singleton types are
    contractible. *)
Definition singleton_contr {X : Type} (a : X) : isContr {x : X & a = x}.
Proof.
  exists (a; refl).
  intros [x i]. destruct i. exact refl.
Defined.

(** Definition [def:fiber], with the convention [y = f x]. *)
Definition fiber {X Y : Type} (f : X -> Y) (y : Y) : Type
  := {x : X & y = f x}.

(** Definition [def:equivalence]. *)
Definition isEquiv {X Y : Type} (f : X -> Y) : Type
  := forall y : Y, isContr (fiber f y).

(** Definition [def:type-of-equivalences]. *)
Definition Eqv (X Y : Type) : Type := {f : X -> Y & isEquiv f}.

Notation "X ≃ Y" := (Eqv X Y) (at level 85) : uf_scope.

(** The inverse of an equivalence: [g(y) :≡ fst(fst(t(y)))]. *)
Section Inverse.

  Context {X Y : Type} {f : X -> Y} (t : isEquiv f).

  Definition eqinv : Y -> X := fun y => fst (fst (t y)).

  Definition eqinv_r (y : Y) : f (eqinv y) = y := (snd (fst (t y)))⁻¹.

  Definition eqinv_l (x : X) : eqinv (f x) = x
    := ap fst (snd (t (f x)) (x; refl)).

End Inverse.

(** The identity function is an equivalence: its fibers are singletons
    (by definition, thanks to the convention [y = f x]). *)
Definition id_isEquiv (X : Type) : isEquiv (id X) := fun a => singleton_contr a.

(** Transport is an equivalence. *)
Definition trp_isEquiv {X : Type} (T : X -> Type) {x y : X} (e : x = y)
  : isEquiv (trp T e)
  := match e with refl => id_isEquiv (T x) end.

(** *** Bridge to Coq-HoTT's [IsEquiv] *)

(** Contractibility is preserved by retracts. *)
Definition isContr_retract {A B : Type} (r : A -> B) (s : B -> A)
  (rs : forall b, r (s b) = b) : isContr A -> isContr B.
Proof.
  intros [c h]. exists (r c).
  intro b. exact (rs b ⋅ ap r (h (s b))).
Defined.

Definition isEquiv_of_IsEquiv {X Y : Type} (f : X -> Y) `{IsEquiv X Y f}
  : isEquiv f.
Proof.
  intro y.
  refine (isContr_retract (A := hfiber f y) (B := fiber f y)
            (fun w => (fst w; (snd w)^)) (fun w => (fst w; (snd w)^)) _ _).
  - intros [x p]. cbn. exact (ap (fun q => (x; q)) (inv_V p)).
  - exact (center (hfiber f y); contr).
Defined.

Definition IsEquiv_of_isEquiv {X Y : Type} {f : X -> Y} (t : isEquiv f)
  : IsEquiv f
  := isequiv_adjointify f (eqinv t) (eqinv_r t) (eqinv_l t).

(** Construction [lem:weq-iso]. *)
Definition isEquiv_to_iso {X Y : Type} {f : X -> Y} (t : isEquiv f)
  : {g : Y -> X & (forall x, g (f x) = x) * (forall y, f (g y) = y)}
  := (eqinv t; (eqinv_l t, eqinv_r t)).

Definition iso_to_isEquiv {X Y : Type} (f : X -> Y) (g : Y -> X)
  (gf : forall x, g (f x) = x) (fg : forall y, f (g y) = y) : isEquiv f
  := isEquiv_of_IsEquiv f (H := isequiv_adjointify f g fg gf).

Definition mkEqv {X Y : Type} (f : X -> Y) (g : Y -> X)
  (gf : forall x, g (f x) = x) (fg : forall y, f (g y) = y) : X ≃ Y
  := (f; iso_to_isEquiv f g gf fg).

Definition Eqv_of_Equiv {X Y : Type} (e : X <~> Y) : X ≃ Y
  := (equiv_fun e; isEquiv_of_IsEquiv e).

(** Exercise [xca:equivalence-invers]. *)
Definition eqinv_isEquiv {X Y : Type} {f : X -> Y} (t : isEquiv f)
  : isEquiv (eqinv t)
  := iso_to_isEquiv (eqinv t) f (eqinv_r t) (eqinv_l t).

Definition Eqv_inv {X Y : Type} : (X ≃ Y) -> (Y ≃ X)
  := fun e => (eqinv (snd e); eqinv_isEquiv (snd e)).

(** Exercise [xca:equivalence-comp]. *)
Definition comp_isEquiv {X Y Z : Type} {f : X -> Y} {g : Y -> Z}
  (s : isEquiv f) (t : isEquiv g) : isEquiv (comp g f).
Proof.
  refine (iso_to_isEquiv _ (comp (eqinv s) (eqinv t)) _ _); intro; unfold comp.
  - exact (ap (eqinv s) (eqinv_l t _) @ eqinv_l s _).
  - exact (ap g (eqinv_r s _) @ eqinv_r t _).
Defined.

Definition Eqv_comp {X Y Z : Type} : (X ≃ Y) -> ((Y ≃ Z) -> (X ≃ Z))
  := fun e e' => (comp (fst e') (fst e); comp_isEquiv (snd e) (snd e')).

(** Exercise [xca:2-out-of-3], with [e : hf = g]. *)
Section TwoOutOfThree.

  Context {A B C : Type} (f : A -> B) (g : A -> C) (h : B -> C)
    (e : comp h f = g).

  Let E (a : A) : h (f a) = g a := ptw e a.

  Definition two_of_three_g (sf : isEquiv f) (sh : isEquiv h) : isEquiv g.
  Proof.
    refine (iso_to_isEquiv g (comp (eqinv sf) (eqinv sh)) _ _); intro; unfold comp.
    - exact (ap (fun c => eqinv sf (eqinv sh c)) (E _)^
               @ ap (eqinv sf) (eqinv_l sh _) @ eqinv_l sf _).
    - exact ((E _)^ @ ap h (eqinv_r sf _) @ eqinv_r sh _).
  Defined.

  Definition two_of_three_h (sf : isEquiv f) (sg : isEquiv g) : isEquiv h.
  Proof.
    refine (iso_to_isEquiv h (comp f (eqinv sg)) _ _); intro b; unfold comp.
    - exact (ap (fun c => f (eqinv sg c))
               (ap h (eqinv_r sf b)^ @ E (eqinv sf b))
             @ ap f (eqinv_l sg _) @ eqinv_r sf b).
    - exact (E _ @ eqinv_r sg b).
  Defined.

  Definition two_of_three_f (sg : isEquiv g) (sh : isEquiv h) : isEquiv f.
  Proof.
    refine (iso_to_isEquiv f (comp (eqinv sg) h) _ _); intro b; unfold comp.
    - exact (ap (eqinv sg) (E b) @ eqinv_l sg b).
    - exact ((eqinv_l sh _)^
             @ ap (eqinv sh) (E _ @ eqinv_r sg (h b)) @ eqinv_l sh b).
  Defined.

End TwoOutOfThree.

(** Lemma [lem:contract-away]. *)
Section ContractAway.

  Context {X : Type} (a : X) (B : forall x, a = x -> Type).

  Definition ca_map : {x : X & {i : a = x & B x i}} -> B a refl
    := fun w => path_ind a (fun x i => B x i -> B a refl) (id _)
                  (fst w) (fst (snd w)) (snd (snd w)).

  Definition ca_map_isEquiv : isEquiv ca_map.
  Proof.
    refine (iso_to_isEquiv ca_map (fun b => (a; refl; b)) _ _).
    - intros [x [i b]]. destruct i. exact refl.
    - intro b. exact refl.
  Defined.

End ContractAway.

(** Corollary [cor:contract-away]; here [(a = x) × B(x)] is the sum over
    a constant family, see 2.11. *)
Definition contract_away {X : Type} (a : X) (B : X -> Type)
  : {x : X & {_ : a = x & B x}} ≃ B a
  := (ca_map a (fun x _ => B x); ca_map_isEquiv a (fun x _ => B x)).

(** Exercise [xca:sum-equiv-base]. *)
Definition sum_equiv_base {X Y : Type} {f : X -> Y} (t : isEquiv f)
  (B : X -> Type) : {x : X & B x} ≃ {y : Y & B (eqinv t y)}
  := Eqv_of_Equiv (equiv_inverse
       (equiv_functor_sigma_pb (Q := B)
          (Build_Equiv _ _ (eqinv t) (IsEquiv_of_isEquiv (eqinv_isEquiv t))))).

(** Definition [def:fiberwise]: totalization of a map of families,
    [tot(f)(x,y) :≡ (x, f(x)(y))]: the library's [functor_sigma idmap]. *)
Definition tot {X : Type} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  : Tot Y -> Tot Z
  := functor_sigma idmap f.

Definition tot_pair {X : Type} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  (x : X) (y : Y x) : tot f (x; y) = (x; f x y) := refl.

(** Lemma [lem:fiberwise] and Exercise [xca:fiberwise]. *)
Definition tot_isEquiv {X : Type} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  (t : forall x, isEquiv (f x)) : isEquiv (tot f).
Proof.
  refine (iso_to_isEquiv (tot f) (tot (fun x => eqinv (t x))) _ _).
  - intros [x y]. exact (ap (fun y' => (x; y')) (eqinv_l (t x) y)).
  - intros [x z]. exact (ap (fun z' => (x; z')) (eqinv_r (t x) z)).
Defined.

(** Lemma [lem:fiberwise-equiv-from-tot] (Theorem 4.7.7 of the HoTT Book). *)
Definition isEquiv_from_tot {X : Type} {Y Z : X -> Type}
  (f : forall x, Y x -> Z x) (t : isEquiv (tot f)) : forall x, isEquiv (f x)
  := fun x => isEquiv_of_IsEquiv (f x)
       (H := @isequiv_from_functor_sigma X Y Z f (IsEquiv_of_isEquiv t) x).

(** Principle [def:funext]: function extensionality postulates
    [funext : isEquiv(ptw_{f,g})].  Since [ptw] is [apD10], this follows
    from Coq-HoTT's axiom [isequiv_apD10], available under [Funext]. *)
Definition funext `{Funext} {X : Type} {Y : X -> Type} (f g : forall x, Y x)
  : isEquiv (@ptw X Y f g)
  := isEquiv_of_IsEquiv ptw (H := isequiv_apD10 X Y f g).

(** The inverse [ptw⁻¹] given by [funext]. *)

Definition ptw_inv `{Funext} {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  : (forall x, f x = g x) -> f = g
  := eqinv (funext f g).

(** Exercise [xca:substitute-away]. *)
Definition substitute_away `{Funext} {X : Type} (a : X) (B : X -> Type)
  : (forall x, a = x -> B x) ≃ B a.
Proof.
  refine (mkEqv (fun h => h a refl) (fun b x i => trp B i b) _ _).
  - intro h. apply ptw_inv; intro x. apply ptw_inv; intro i.
    destruct i. exact refl.
  - intro b. exact refl.
Defined.

(** Exercise [xca:Xequiv1toX]. *)
Definition True_to_X_eqv `{Funext} (X : Type) : (True -> X) ≃ X.
Proof.
  refine (mkEqv (fun f => f triv) (fun x => cst x) _ _).
  - intro f. apply ptw_inv. intros []. exact refl.
  - intro x. exact refl.
Defined.

(** Exercise [xca:XequivXtimes1]. *)
Definition sum_True_eqv (X : Type) : {_ : X & True} ≃ X.
Proof.
  refine (mkEqv fst (fun x => (x; triv)) _ _).
  - intros [x []]. exact refl.
  - intro x. exact refl.
Defined.

(** Exercise [xca:Sigma-distrib]. *)
Definition sigma_distrib (X Y : Type) (Z : Y -> Type)
  : {_ : X & {y : Y & Z y}} ≃ {y : Y & {_ : X & Z y}}
  := mkEqv (fun w : {_ : X & {y : Y & Z y}} => (fst (snd w); fst w; snd (snd w)))
           (fun w : {y : Y & {_ : X & Z y}} => (fst (snd w); fst w; snd (snd w)))
           (fun _ => refl) (fun _ => refl).

(** Exercise [xca:Sigma-comm]. *)
Definition sigma_comm (X Y : Type) (Z : X -> Y -> Type)
  : {x : X & {y : Y & Z x y}} ≃ {y : Y & {x : X & Z x y}}
  := mkEqv (fun w : {x : X & {y : Y & Z x y}} => (fst (snd w); fst w; snd (snd w)))
           (fun w : {y : Y & {x : X & Z x y}} => (fst (snd w); fst w; snd (snd w)))
           (fun _ => refl) (fun _ => refl).

(** Footnote [ft:Sigma-assoc]: associativity of sum types. *)
Definition sigma_assoc (X : Type) (Y : X -> Type)
  (Z : forall x, Y x -> Type)
  : {x : X & {y : Y x & Z x y}} ≃ {w : {x : X & Y x} & Z (fst w) (snd w)}
  := mkEqv (fun w : {x : X & {y : Y x & Z x y}} =>
              ((fst w; fst (snd w)) : {x : X & Y x}; snd (snd w)))
           (fun w : {w : {x : X & Y x} & Z (fst w) (snd w)} =>
              (fst (fst w); snd (fst w); snd w))
           (fun _ => refl) (fun _ => refl).

(** Exercise [xca:fib-of-comp]. *)
Definition fib_of_comp {X Y Z : Type} (f : X -> Y) (g : Y -> Z) (z : Z)
  : fiber (comp g f) z ≃ {w : fiber g z & fiber f (fst w)}.
Proof.
  refine (mkEqv (fun v : fiber (comp g f) z =>
                   ((f (fst v); snd v) : fiber g z; (fst v; refl) : fiber f _))
                (fun w : {w : fiber g z & fiber f (fst w)} =>
                   (fst (snd w); ap g (snd (snd w)) ⋅ snd (fst w)))
                (fun _ => refl) _).
  intros [[y p] [x q]]. cbn in *.
  revert y q p. refine (paths_ind_r _ _ _). intro p. exact refl.
Defined.

(** Exercise [xca:AC-in-TT]: holds with round trips by definition. *)
Definition type_theoretic_AC (X Y : Type) (Z : X -> Y -> Type)
  : (forall x, {y : Y & Z x y}) ≃ {f : X -> Y & forall x, Z x (f x)}
  := mkEqv (fun h : forall x, {y : Y & Z x y} =>
              ((fun x => fst (h x)); (fun x => snd (h x)))
              : {f : X -> Y & forall x, Z x (f x)})
           (fun w : {f : X -> Y & forall x, Z x (f x)} =>
              fun x => (fst w x; snd w x) : {y : Y & Z x y})
           (fun _ => refl) (fun _ => refl).

(** Exercise [xca:section-above-f]. *)
Section SectionAboveF.

  Context {X Z : Type} {Y : X -> Type} (f : Z -> X).

  Let fwd (s : forall z, Y (f z))
    : {g : Z -> {x : X & Y x} & f = comp fst g}
    := ((fun z => (f z; s z)); refl).

  Let bwd (w : {g : Z -> {x : X & Y x} & f = comp fst g})
    : forall z, Y (f z)
    := fun z => trp Y (ptw (snd w) z)⁻¹ (snd (fst w z)).

  Local Definition fwd_bwd_gen (g1 : Z -> X) (g2 : forall z, Y (g1 z))
    (e : f = g1)
    : fwd (bwd ((fun z => (g1 z; g2 z)); e)) = ((fun z => (g1 z; g2 z)); e).
  Proof. destruct e. exact refl. Defined.

  Definition section_above_f
    : (forall z, Y (f z)) ≃ {g : Z -> {x : X & Y x} & f = comp fst g}.
  Proof.
    refine (mkEqv fwd bwd (fun _ => refl) _).
    intros [g e]. exact (fwd_bwd_gen (comp fst g) (fun z => snd (g z)) e).
  Defined.

End SectionAboveF.

(** Exercise [xca:Sigma-curry]. *)
Definition sigma_curry (X Z : Type) (Y : X -> Type)
  : ({x : X & Y x} -> Z) ≃ (forall x, Y x -> Z)
  := mkEqv (fun (h : {x : X & Y x} -> Z) x y => h (x; y))
           (fun (k : forall x, Y x -> Z) (w : {x : X & Y x}) => k (fst w) (snd w))
           (fun _ => refl) (fun _ => refl).

(** ** 2.10 Identifying pairs *)

Section IdentifyingPairs.

  Context {X : Type} {Y : X -> Type}.

  (** Definition [def:pairtopath]. *)
  Definition pair : forall x : X, Y x -> Tot Y := exist Y.

  Definition pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y') : (x; y) = (x'; y')
    := apap pair p q.

  (** Construction [cor:isEquiv-pair=]. *)
  Definition pathpair_refl {x : X} {y y' : Y x} (q : y = y')
    : pathpair refl q = ap (pair x) q
    := apap_refl pair q.

  (** The inverse map [Ψ], for arbitrary elements of the sum type. *)
  Definition pathsplit {w w' : Tot Y} (r : w = w')
    : {p : fst w = fst w' & PathOver Y p (snd w) (snd w')}
    := match r with refl => (refl; refl) end.

  Definition pathsplit_pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y')
    : pathsplit (pathpair p q) = (p; q).
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

  Definition pathpair_pathsplit {w w' : Tot Y} (r : w = w')
    : pathpair (fst (pathsplit r)) (snd (pathsplit r)) = r.
  Proof. destruct r. exact refl. Defined.

  (** Lemma [lem:isEquiv-pair=]. *)
  Definition pathpair_isEquiv {x x' : X} {y : Y x} {y' : Y x'}
    : isEquiv (fun pq : {p : x = x' & PathOver Y p y y'} =>
              pathpair (fst pq) (snd pq))
    := iso_to_isEquiv _ pathsplit
         (fun pq => pathsplit_pathpair (fst pq) (snd pq))
         pathpair_pathsplit.

  Definition path_sigma_eqv {x x' : X} {y : Y x} {y' : Y x'}
    : {p : x = x' & PathOver Y p y y'} ≃ ((x; y) = (x'; y'))
    := (_; pathpair_isEquiv).

  (** [fst(pair^=(p,q)) = p], [snd(pair^=(p,q)) = q] (combined in
      [pathsplit_pathpair] above), and [r = pair^=(fst(r), snd(r))]
      (this is [pathpair_pathsplit]). *)
  Definition ap_fst_pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y')
    : ap fst (pathpair p q) = p.
  Proof. destruct p. cbn in q. destruct q. exact refl. Defined.

  Definition fst_pathsplit {w w' : Tot Y} (r : w = w')
    : fst (pathsplit r) = ap fst r
    := match r with refl => refl end.

End IdentifyingPairs.

(** ** 2.11 Binary products

    The binary product [X × Y] is the sum over the constant family [Y]. *)

Notation "X × Y" := ({_ : X & Y})
  : uf_scope.

(** It is equivalent to Coq-HoTT's record type [prod]. *)
Definition binprod_prod (X Y : Type) : (X × Y) ≃ (X * Y)
  := mkEqv (fun w : X × Y => (fst w, snd w)) (fun w : X * Y => (Overture.fst w; Overture.snd w) : X × Y)
           (fun _ => refl) (fun _ => refl).

(** Paths over a path in a constant family are paths, as an equivalence. *)
Definition po_const {X Z : Type} {a a' : X} (p : a = a') {z z' : Z}
  : (z = z') -> PathOver (fun _ => Z) p z z'
  := match p with refl => id _ end.

Definition po_const_isEquiv {X Z : Type} {a a' : X} (p : a = a') (z z' : Z)
  : isEquiv (@po_const X Z a a' p z z')
  := match p with refl => id_isEquiv _ end.

(** Lemma [lem:isEquiv-pair-bin=]. *)
Definition pathpair_bin {X Y : Type} {x x' : X} {y y' : Y}
  : (x = x') × (y = y') -> ((x; y) = (x'; y') :> X × Y)
  := fun pq => pathpair (fst pq) (po_const (fst pq) (snd pq)).

Definition pathpair_bin_isEquiv {X Y : Type} {x x' : X} {y y' : Y}
  : isEquiv (@pathpair_bin X Y x x' y y')
  := comp_isEquiv (tot_isEquiv _ (fun p => po_const_isEquiv p y y')) pathpair_isEquiv.

Definition path_prod_eqv {X Y : Type} (x x' : X) (y y' : Y)
  : ((x = x') × (y = y')) ≃ ((x; y) = (x'; y') :> X × Y)
  := (_; pathpair_bin_isEquiv).

(** The product of two maps. *)
Definition prod_map {X X' Y Y' : Type} (f : X -> Y) (f' : X' -> Y')
  : X × X' -> Y × Y'
  := fun w => (f (fst w); f' (snd w)).

(** Exercise [xca:binary-prod-equiv]. *)
Definition bool_family (X Y : Type) : Bool -> Type
  := fun b => if b then Y else X.

Definition binary_prod_equiv `{Funext} (X Y : Type)
  : isEquiv (fun f : forall b, bool_family X Y b => (f no; f yes) : X × Y).
Proof.
  refine (iso_to_isEquiv _
            (fun (w : X × Y) b => match b return bool_family X Y b with
                                  | yes => snd w | no => fst w end)
            _ (fun _ => refl)).
  intro f. apply ptw_inv. intros []; exact refl.
Defined.

(** Exercise [xca:binary-prod-comm]. *)
Definition binary_prod_comm (X Y : Type) : (X × Y) ≃ (Y × X)
  := mkEqv (fun w : X × Y => (snd w; fst w) : Y × X)
           (fun w : Y × X => (snd w; fst w) : X × Y)
           (fun _ => refl) (fun _ => refl).

(** ** 2.12 More inductive types *)

(** *** Finite types: [False] ([𝟘]), [True] ([𝟙] with [triv :≡ triv]) and
    [Bool] ([𝟚]), all in [Type0]. *)

Check (False : Type0).
Check (True : Type0).
Check (Bool : Type0).

Definition False_paths (x y : False) : x = y := match x with end.

Definition False_absurd_nat : False -> (0%nat = 1%nat :> ℕ)
  := fun x => match x with end.

Definition True_center (u : True) : u = triv
  := match u with triv => refl end.

Definition True_paths (x y : True) : x = y
  := match x, y with triv, triv => refl end.

Definition to_Unit (X : Type) : X -> True := fun _ => triv.

(** Exercise [xca:True-univ-prop]. *)
Definition True_univ_prop `{Funext} (X : Type)
  : isEquiv (fun f : True -> X => f triv)
  := snd (True_to_X_eqv X).

(** [(yes = no) -> 𝟘], by substitution in [P(yes) :≡ 𝟙], [P(no) :≡ 𝟘]. *)
Definition yes_ne_no : (yes = no) -> False
  := fun e => trp (fun b : Bool => if b then True else False) e triv.

(** [(0 = S(n)) -> 𝟘], by substitution in [P(0) :≡ 𝟙], [P(S(m)) :≡ 𝟘]. *)
Definition zero_ne_succ (n : ℕ) : (0%nat = succ n) -> False
  := fun e => trp (fun i : ℕ => match i with O => True | S _ => False end)
                e triv.

(** *** Binary sums: [X ⨿ Y] is Coq-HoTT's [X + Y]. *)

Notation "X ⨿ Y" := (sum X Y) (at level 50, left associativity) : uf_scope.

(** Exercise [xca:binary-sum-equiv]. *)
Definition binary_sum_equiv (X Y : Type)
  : isEquiv (fun z : X ⨿ Y =>
            match z return {b : Bool & bool_family X Y b} with
            | inl x => (no; x)
            | inr y => (yes; y)
            end).
Proof.
  refine (iso_to_isEquiv _
            (fun w => match w with
                      | (yes; y) => inr y
                      | (no; x) => inl x
                      end) _ _).
  - intros [x|y]; exact refl.
  - intros [[] t]; exact refl.
Defined.

(** Exercise [xca:binary-sum-id].  We use the encode-decode method instead
    of the suggested route via [xca:binary-sum-equiv]. *)
Section BinarySumPaths.

  Context {X Y : Type}.

  Definition code_inl (x : X) : X ⨿ Y -> Type
    := fun w => match w with inl x' => x = x' | inr _ => False end.

  Definition code_inr (y : Y) : X ⨿ Y -> Type
    := fun w => match w with inl _ => False | inr y' => y = y' end.

  Definition encode_inl {x : X} {w : X ⨿ Y} (r : inl x = w) : code_inl x w
    := trp (code_inl x) r refl.

  Definition encode_inr {y : Y} {w : X ⨿ Y} (r : inr y = w) : code_inr y w
    := trp (code_inr y) r refl.

  Definition inl_ne_inr (x : X) (y : Y) : (inl x = inr y) -> False
    := encode_inl.

  Definition path_inl_eqv (x x' : X) : (inl x = inl x' :> X ⨿ Y) ≃ (x = x').
  Proof.
    refine (mkEqv (@encode_inl x (inl x')) (ap inl) _ _).
    - intro r.
      enough (G : forall w (r : inl x = w),
                 match w return inl x = w -> Type with
                 | inl x' => fun r => ap inl (encode_inl r) = r
                 | inr _ => fun _ => True
                 end r) by exact (G _ r).
      intros w r'. destruct r'. exact refl.
    - intro p. destruct p. exact refl.
  Defined.

  Definition path_inr_eqv (y y' : Y) : (inr y = inr y' :> X ⨿ Y) ≃ (y = y').
  Proof.
    refine (mkEqv (@encode_inr y (inr y')) (ap inr) _ _).
    - intro r.
      enough (G : forall w (r : inr y = w),
                 match w return inr y = w -> Type with
                 | inl _ => fun _ => True
                 | inr y' => fun r => ap inr (encode_inr r) = r
                 end r) by exact (G _ r).
      intros w r'. destruct r'. exact refl.
    - intro p. destruct p. exact refl.
  Defined.

End BinarySumPaths.

(** Exercise [xca:bin-sum-univ-prop]. *)
Definition bin_sum_univ_prop `{Funext} (X Y Z : Type)
  : isEquiv (fun h : X ⨿ Y -> Z => (comp h inl; comp h inr) : (X -> Z) × (Y -> Z)).
Proof.
  refine (iso_to_isEquiv _
            (fun (w : (X -> Z) × (Y -> Z)) z =>
               match z with inl x => fst w x | inr y => snd w y end)
            _ (fun _ => refl)).
  intro h. apply ptw_inv. intros [x|y]; exact refl.
Defined.

(** Exercise: [(X ⨿ 𝟘) ≃ X]. *)
Definition sum_False_eqv (X : Type) : (X ⨿ False) ≃ X.
Proof.
  refine (mkEqv (fun z : X ⨿ False =>
                   match z with inl x => x | inr e => match e with end end)
                inl _ (fun _ => refl)).
  intros [x|[]]. exact refl.
Defined.

(** *** Unary sums *)

Inductive Copy (X : Type) : Type := inc : X -> Copy X.
Arguments inc {X} x.

(** The destructor [out(inc(x)) :≡ x]. *)
Definition out {X : Type} (z : Copy X) : X := match z with inc x => x end.

Definition inc_out {X : Type} (z : Copy X) : inc (out z) = z
  := match z with inc x => refl end.

Definition Copy_eqv (X : Type) : Copy X ≃ X
  := mkEqv out inc inc_out (fun _ => refl).

Definition path_inc_eqv {X : Type} (x x' : X) : (inc x = inc x') ≃ (x = x').
Proof.
  refine (mkEqv (@ap _ _ out (inc x) (inc x')) (@ap _ _ inc x x') _ _).
  - intro r.
    enough (G : forall w (r : inc x = w),
               match w return inc x = w -> Type with
               | inc x' => fun r => ap inc (ap out r) = r
               end r) by exact (G _ r).
    intros w r'. destruct r'. exact refl.
  - intro p. change (x = x') in p. destruct p. exact refl.
Defined.

Definition path_out_eqv {X : Type} (z z' : Copy X) : (out z = out z') ≃ (z = z').
Proof. destruct z as [x], z' as [x']. exact (Eqv_inv (path_inc_eqv x x')). Defined.

(** Example [exa:nnn]: the negated natural numbers [ℕ⁻ :≡ Copy_{-}(ℕ)]; the constructor
    [-] is called [negN], since [neg] is negation (2.15). *)
Inductive NNN : Type0 := negN : ℕ -> NNN.

(** The destructor [-(-n) :≡ n]. *)
Definition unneg (m : NNN) : ℕ := match m with negN n => n end.

Definition neg_unneg_neg (n : ℕ) : negN (unneg (negN n)) = negN n := refl.

Definition NNN_eqv : NNN ≃ ℕ
  := mkEqv unneg negN (fun m => match m with negN n => refl end)
           (fun _ => refl).

(** *** Lists

    Definition [def:lists]: [X^*] is the library's [list X], with the
    empty list [ε :≡ nil] and the constructor [cons]. *)

Notation "X ^*" := (list X) (at level 1, format "X ^*") : uf_scope.
Notation ε := nil.

(** The induction principle is the library's [list_ind], with its
    computation rules holding by definition. *)
Definition list_ind_nil {X : Type} (T : X^* -> Type) (t : T ε)
  (g : forall x l, T l -> T (cons x l))
  : list_ind X T t g ε = t := refl.
Definition list_ind_cons {X : Type} (T : X^* -> Type) (t : T ε)
  (g : forall x l, T l -> T (cons x l)) (x : X) (l : X^*)
  : list_ind X T t g (cons x l) = g x l (list_ind X T t g l) := refl.

(** The length, [len(ε) :≡ 0] and [len(x l) :≡ succ(len(l))]: the
    library's [length]. *)
Definition len {X : Type} : X^* -> ℕ := @length X.

Definition len_nil {X : Type} : len (ε : X^*) = 0%nat := refl.
Definition len_cons {X : Type} (x : X) (l : X^*)
  : len (cons x l) = succ (len l) := refl.

(** Exercise [xca:list-contr], using the library's [repeat]. *)
Definition len_isEquiv {X : Type} (H : isContr X) : isEquiv (@len X).
Proof.
  refine (iso_to_isEquiv len (repeat (fst H)) _ _).
  - intro l. induction l as [|x l IH].
    + exact refl.
    + exact (ap011 cons (snd H x) IH).
  - intro n. induction n as [|n IH].
    + exact refl.
    + exact (ap succ IH).
Defined.

(** Head and tail, with values in [X ⨿ True] as in the book.  (The
    library's [head] uses [option], and its [tail] maps [ε] to [ε].) *)
Definition hd {X : Type} (l : X^*) : X ⨿ True
  := match l with ε => inr triv | cons x _ => inl x end.

Definition tl {X : Type} (l : X^*) : X^* ⨿ True
  := match l with ε => inr triv | cons _ l' => inl l' end.

(** Exercise [xca:reverse]: concatenation, by induction on the first
    argument, is the library's [app]; reversal is defined from it.  (The
    library's [reverse] uses an accumulator instead.) *)
Definition app_nil {X : Type} (l : X^*) : app ε l = l := refl.
Definition app_cons {X : Type} (x : X) (l1 l2 : X^*)
  : app (cons x l1) l2 = cons x (app l1 l2) := refl.

Definition rev {X : Type} : X^* -> X^*
  := list_ind X (fun _ => X^*) ε (fun x _ r => app r (cons x ε)).

(** Exercise [xca:concat-assoc]. *)
Definition app_assoc {X : Type} (l1 l2 l3 : X^*)
  : app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
  induction l1 as [|x l1 IH].
  - exact refl.
  - exact (ap (cons x) IH).
Defined.

(** * Part 3: Sections 2.13 - 2.15

    ** Summary of this formalization

    Sections 2.13 - 2.15 are formalized in this file, which builds on
    [IntroUF.v] and [IntroUF2.v].  It compiles.  [Print Assumptions]
    shows that the only axiom used is Coq-HoTT's [Funext], and only by
    the results that need it.  The exception is the derivation of the
    book's univalence axiom, which uses the library's [Univalence], as
    intended.

    Book notions defined from Coq-HoTT notions: [neg := not] (notation
    [¬]); [ptoe p] is [trp] in the identity family, and the library's
    [negb] is the swap of [Bool].  Own definitions, because the library's
    notions differ: [isProp P :≡ ∏_{a,b:P} (a = b)], [isSet], [isGrpd]
    and [is_ntype n] (the library's [IsHProp], [IsHSet], [IsTrunc] are
    defined via contractibility), inequality [≠], [idtoeqv] into the
    book's type [≃] of equivalences, and the class [UnivalenceUF].

    2.13 Univalence
    - The book's axiom is a class [UnivalenceUF := ∀ X Y, isEquiv idtoeqv].
      Its inverse is [etop] (the book's [f̄]).  The four identifications
      listed in the text are proved: [etop (ptoe p) = p] and
      [ptoe (etop f) = f]; [etop id = refl]; [etop (g f) = etop g · etop f].
    - Exercise [xca:C2]: every [p : Bool = Bool] is either [refl] or
      [swap], [refl ≠ swap], and [swap · swap = refl].
    - At the end of the file an instance of [UnivalenceUF] is derived
      from Coq-HoTT's [Univalence].  This needs the fact that
      [isEquiv f] is a proposition, which the book only proves in 2.15;
      a short preliminary obtains it from the library.

    2.14 Heavy transport
    - Transport in function-type families, and its univalence special
      case: transport along [etop g] gives [g ∘ f ∘ g⁻¹].
    - Transport in [f x = g x] and its four special cases (the last is
      conjugation), plus the dependent version stated with [po_e(apd …)].
    - [trptw] (pointwise transport).
    - Dan's lemma, formalized literally as written:
      [(f(x) =^Y_p f(x')) ≃ (f(x) = f(x))].  The right-hand side and the
      [e]/[p] mix-up in the statement look like typos in the source.

    2.15 Propositions, sets and groupoids
    - [isProp], [isSet], [isGrpd], [is_ntype n] (for n ≥ 0), [¬], [≠].
    - Every proposition is a set, following the book's argument.
    - [Bool] is a set, via Simon Huber's proof.
    - All six parts of [lem:prop-utils], plus the fact that [True ⨿ True]
      is not a proposition.
    - [lem:level-n-utils], which the book states without proof, by
      comparing [is_ntype] with Coq-HoTT's [IsTrunc].
    - [isContr], [isProp], [isSet], [isGrpd], [is_ntype n] and
      [isEquiv f] are all propositions; the [isContr] case follows the
      book's proof.
    - A type is a proposition exactly when all its identity types are
      contractible.
    - The diagrams remark has no formal content, so it is only a comment.

    ** Conventions

    Continuation of [IntroUF.v] and [IntroUF2.v], with the same
    conventions: path composition [q ⋅ p :≡ p ∙ q], fibers with
    [y = f x], and notions that occur definitionally in Coq-HoTT defined
    from the library notion and used under the book's name.

    The univalence axiom is stated as in the book, as a class
    [UnivalenceUF] postulating [isEquiv(p ↦ ptoe p)].  At the end of the
    file we derive an instance from Coq-HoTT's axiom [Univalence].
    As in [IntroUF2.v], function extensionality is used through the
    book's principle [funext : isEquiv(ptw)], derived from Coq-HoTT's
    [Funext], and only where needed. *)

(** ** Preliminaries: identifying equivalences

    Two equivalences can be identified as soon as their underlying
    functions can, because [isEquiv(f)] is a proposition (shown in the book
    in 2.15, see [isEquiv_isProp] below).  Here we obtain it from the
    library, so that 2.13 can be presented before 2.15. *)

(** [isContr(X)] is a retract of Coq-HoTT's [Contr X], which is an
    h-proposition. *)
Instance ishprop_isContr `{Funext} (X : Type) : IsHProp (isContr X).
Proof.
  apply hprop_allpath. intros a b.
  exact (ap (fun C : Contr X => (center X; contr) : isContr X)
            (path_ishprop (Build_Contr _ (fst a) (snd a))
                          (Build_Contr _ (fst b) (snd b)))).
Defined.

Instance ishprop_isEquiv `{Funext} {X Y : Type} (f : X -> Y)
  : IsHProp (isEquiv f)
  := istrunc_forall.

Definition path_Eqv `{Funext} {X Y : Type} (e e' : X ≃ Y)
  : fst e = fst e' -> e = e'
  := path_sigma_hprop e e'.

Definition idEqv (X : Type) : X ≃ X := (id X; id_isEquiv X).

(** ** 2.13 Univalence *)

(** Definition [def:idtoeq]: transport in the family [id_U]. *)
Definition ptoe {X Y : Type} (p : X = Y) : X -> Y
  := trp (fun T : Type => T) p.

Definition idtoeqv {X Y : Type} (p : X = Y) : X ≃ Y
  := (ptoe p; trp_isEquiv (fun T : Type => T) p).

Definition idtoeqv_refl (X : Type) : idtoeqv (refl X) = idEqv X := refl.

(** Principle [def:univalence]: the univalence axiom postulates
    [ua_{X,Y} : isEquiv(p ↦ ptoe p)]. *)
Class UnivalenceUF := ua : forall X Y : Type, isEquiv (@idtoeqv X Y).

Section Univalence.

  Context `{UnivalenceUF}.

  (** The inverse [f ↦ etop f] (the book's [\bar f]). *)
  Definition etop {X Y : Type} (f : X ≃ Y) : X = Y := eqinv (ua X Y) f.

  Definition etop_ptoe {X Y : Type} (p : X = Y) : etop (idtoeqv p) = p
    := eqinv_l (ua X Y) p.

  Definition ptoe_etop {X Y : Type} (f : X ≃ Y) : idtoeqv (etop f) = f
    := eqinv_r (ua X Y) f.

  Definition etop_id (X : Type) : etop (idEqv X) = refl
    := etop_ptoe refl.

  Context `{Funext}.

  (** [ptoe] turns composition of paths into composition of
      equivalences ([xca:trp-compose]). *)
  Definition idtoeqv_trans {X Y Z : Type} (p : X = Y) (q : Y = Z)
    : idtoeqv (q ⋅ p) = Eqv_comp (idtoeqv p) (idtoeqv q)
    := path_Eqv (idtoeqv (q ⋅ p)) (Eqv_comp (idtoeqv p) (idtoeqv q))
         (trp_compose (fun T : Type => T) p q).

  (** [etop (g f) = etop g · etop f]. *)
  Definition etop_comp {X Y Z : Type} (f : X ≃ Y) (g : Y ≃ Z)
    : etop (Eqv_comp f g) = etop g ⋅ etop f.
  Proof.
    refine (ap etop (ap011 Eqv_comp (ptoe_etop f)^ (ptoe_etop g)^) @ _).
    refine (ap etop (idtoeqv_trans (etop f) (etop g))^ @ _).
    exact (etop_ptoe _).
  Defined.

  (** Exercise [xca:C2]. *)
  Definition negb_isEquiv : isEquiv negb
    := iso_to_isEquiv negb negb (fun b => match b with yes | no => refl end)
         (fun b => match b with yes | no => refl end).

  Definition swapEqv : Bool ≃ Bool := (negb; negb_isEquiv).

  Definition swap : Bool = Bool :> Type := etop swapEqv.

  (** Every equivalence [Bool -> Bool] is the identity or [negb]. *)
  Definition bool_eqv_cases (f : Bool -> Bool) (t : isEquiv f)
    : (f = id Bool) + (f = negb).
  Proof.
    assert (inj : forall b b', f b = f b' -> b = b').
    { intros b b' e. exact ((eqinv_l t b)^ @ ap (eqinv t) e @ eqinv_l t b'). }
    enough (G : forall b1 b2, f yes = b1 -> f no = b2 -> (f = id Bool) + (f = negb))
      by exact (G _ _ refl refl).
    intros [] [] e1 e2.
    - destruct (yes_ne_no (inj _ _ (e1 @ e2^))).
    - left. apply ptw_inv. intros []; assumption.
    - right. apply ptw_inv. intros []; assumption.
    - destruct (yes_ne_no (inj _ _ (e1 @ e2^))).
  Defined.

  (** [Bool = Bool] has exactly two elements: [refl] and [swap]. *)
  Definition Bool_paths_cases (p : Bool = Bool :> Type)
    : (p = refl) + (p = swap).
  Proof.
    destruct (bool_eqv_cases (ptoe p) (snd (idtoeqv p))) as [e|e].
    - left.
      exact ((etop_ptoe p)^ @ ap etop (path_Eqv (idtoeqv p) (idEqv Bool) e)
             @ etop_id Bool).
    - right.
      exact ((etop_ptoe p)^ @ ap etop (path_Eqv (idtoeqv p) swapEqv e)).
  Defined.

  Definition refl_ne_swap : (refl (Bool : Type) = swap) -> False.
  Proof.
    intro e.
    pose (e' := ap (fun p => fst (idtoeqv p)) e @ ap fst (ptoe_etop swapEqv)).
    exact (yes_ne_no (ptw e' yes)).
  Defined.

  Definition swap_swap : swap ⋅ swap = refl.
  Proof.
    refine ((etop_comp swapEqv swapEqv)^ @ _ @ etop_id Bool).
    apply ap, path_Eqv, ptw_inv. intros []; exact refl.
  Defined.

End Univalence.

(** ** 2.14 Heavy transport *)

(** Definition [def:function-type-families]. *)
Definition fun_family {X : Type} (Y Z : X -> Type) : X -> Type
  := fun x => Y x -> Z x.

(** Construction [lem:trp-in-function-type]. *)
Definition trp_fun {X : Type} {Y Z : X -> Type} {x x' : X} (e : x = x')
  (f : Y x -> Z x) (y' : Y x')
  : trp (fun_family Y Z) e f y' = trp Z e (f (trp Y e⁻¹ y')).
Proof. destruct e. exact refl. Defined.

(** The special case [Y :≡ Z :≡ id_U] with a path coming from univalence:
    [trp^{X ↦ (X → X)}_{etop g}(f) = g ∘ f ∘ g⁻¹]. *)
Definition trp_trp_inv {A B : Type} (p : A = B) (b : B)
  : ptoe p (trp (fun T : Type => T) p⁻¹ b) = b.
Proof. destruct p. exact refl. Defined.

Definition trp_endo_gen `{Funext} {A B : Type} (p : A = B) (g : A ≃ B)
  (h : ptoe p = fst g) (f : A -> A)
  : trp (fun X : Type => X -> X) p f = comp (fst g) (comp f (eqinv (snd g))).
Proof.
  apply ptw_inv. intro b.
  refine (trp_fun (Y := fun T : Type => T) (Z := fun T : Type => T) p f b @ _).
  unfold comp.
  refine (ptw h _ @ ap (fun a => fst g (f a)) _).
  refine ((eqinv_l (snd g) _)^ @ ap (eqinv (snd g)) _).
  exact ((ptw h _)^ @ trp_trp_inv p b).
Defined.

Definition trp_endo_ua `{UnivalenceUF} `{Funext} {A B : Type} (g : A ≃ B)
  (f : A -> A)
  : trp (fun X : Type => X -> X) (etop g) f
    = comp (fst g) (comp f (eqinv (snd g)))
  := trp_endo_gen (etop g) g (ap fst (ptoe_etop g)) f.

(** Construction [lem:trp-in-fx=Ygx]:
    [trp^Z_e(i) = ap_g(e) · i · ap_f(e)⁻¹], where [Z(x) :≡ (f(x) = g(x))]. *)
Definition trp_paths_fg {X Y : Type} (f g : X -> Y) {x x' : X} (e : x = x')
  (i : f x = g x)
  : trp (fun x => f x = g x) e i = (ap g e ⋅ i) ⋅ (ap f e)⁻¹.
Proof. destruct e. exact (trans_1p i)^. Defined.

(** Exercise [xca:trp-in-a/x=b/x]. *)
Section TrpInPaths.

  Context {X : Type} (a b : X) {x x' : X} (e : x = x').

  Definition trp_paths_const (i : a = b) : trp (fun _ => a = b) e i = i.
  Proof. destruct e. exact refl. Defined.

  Definition trp_paths_l (i : a = x) : trp (fun x => a = x) e i = e ⋅ i.
  Proof. destruct e. exact refl. Defined.

  Definition trp_paths_r (i : x = b) : trp (fun x => x = b) e i = i ⋅ e⁻¹.
  Proof. destruct e. exact (trans_1p i)^. Defined.

  (** Conjugation; see also [trp_symmetry_conj] in [IntroUF.v]. *)
  Definition trp_paths_conj (i : x = x)
    : trp (fun x => x = x) e i = (e ⋅ i) ⋅ e⁻¹.
  Proof. destruct e. exact (trans_1p i)^. Defined.

End TrpInPaths.

(** Converting a path over [p] into a path using transport, via [po_p]. *)
Definition po_to_trp {X : Type} {Y : X -> Type} {x x' : X} {p : x = x'}
  {y : Y x} {y' : Y x'} (q : PathOver Y p y y') : trp Y p y = y'
  := trp (fun T : Type => T) (po p y y') q.

(** Construction [lem:trp-in-fx=Yxgx]: the dependent version. *)
Definition trp_paths_dep {X : Type} {Y : X -> Type} (f g : forall x, Y x)
  {x x' : X} (e : x = x') (i : f x = g x)
  : trp (fun x => f x = g x) e i
    = (po_to_trp (apd g e) ⋅ ap (trp Y e) i) ⋅ (po_to_trp (apd f e))⁻¹.
Proof.
  destruct e. cbn.
  exact ((ap_id i)^ @ (trans_1p (ap (id (Y x)) i))^).
Defined.

(** Definition [def:Dan's-lemma], stated literally as in the text:
    [(f(x) =^Y_p f(x')) ≃ (f(x) = f(x))], by induction on [p]. *)
Definition dans_lemma {X : Type} {Y : X -> Type} (f : forall x, Y x)
  {x x' : X} (p : x = x')
  : PathOver Y p (f x) (f x') ≃ (f x = f x).
Proof. destruct p. exact (idEqv _). Defined.

(** Exercise [xca:trp-in-y=_(x)]: pointwise transport. *)
Definition trptw {X Y : Type} {x : X} {y : Y} {f g : X -> Y} (e : f = g)
  (p : y = f x)
  : trp (fun h : X -> Y => y = h x) e p = ptw e x ⋅ p.
Proof. destruct e. exact refl. Defined.

(** ** 2.15 Propositions, sets and groupoids *)

(** Definition [def:isSet]. *)
Definition isProp (P : Type) : Type := forall a b : P, a = b.
Definition isSet (S : Type) : Type := forall x y : S, isProp (x = y).
Definition isGrpd (G : Type) : Type := forall g h : G, isSet (g = h).

(** [n]-types for [n ≥ 0]: [X] is an [(n+1)]-type if all its identity
    types are [n]-types. *)
Fixpoint is_ntype (n : ℕ) (X : Type) : Type
  := match n with
     | O => isSet X
     | S n => forall x y : X, is_ntype n (x = y)
     end.

Definition is_ntype_1 (X : Type) : is_ntype 1 X = isGrpd X := refl.

(** Definition [def:neg-eq-ne]: negation [¬P :≡ (P -> ∅)], the library's
    [not], and inequality [a ≠ b :≡ ¬(a = b)]. *)
Definition neg (P : Type) : Type := not P.
Notation "¬ P" := (neg P) : uf_scope.

Definition ne {A : Type} (a b : A) : Type := ¬ (a = b).
Notation "a ≠ b" := (ne a b) (at level 70) : uf_scope.

Definition yes_ne_no' : yes ≠ no := yes_ne_no.

(** Lemma [lem:prop-is-set]. *)
Definition prop_is_set {X : Type} (f : isProp X) : isSet X.
Proof.
  (* [q · f(a,b) = f(a,c)] for [q : b = c], by induction on [q]. *)
  assert (K : forall a b c (q : b = c), q ⋅ f a b = f a c).
  { intros a b c q. destruct q. exact refl. }
  (* Hence [q = f(b,c) · f(b,b)⁻¹], which doesn't depend on [q]. *)
  assert (L : forall b c (q : b = c), q = f b c ⋅ (f b b)⁻¹).
  { intros b c q. destruct q. exact (trans_Vp (f b b))^. }
  intros x y p q. exact (L x y p @ (L x y q)^).
Defined.

(** Lemma [lem:isSet-bool], following Simon Huber's proof. *)
Definition C_bool (b b' : Bool) : b = b' -> Type
  := match b, b' with
     | yes, yes => fun p => p = refl
     | no, no => fun p => p = refl
     | _, _ => fun _ => True
     end.

Definition C_bool_all (b b' : Bool) (p : b = b') : C_bool b b' p.
Proof. destruct p, b; exact refl. Defined.

Definition bool_loops_trivial (b : Bool) (p : b = b) : p = refl.
Proof. destruct b; exact (C_bool_all _ _ p). Defined.

Definition isSet_bool : isSet Bool.
Proof. intros b b' p q. destruct q. exact (bool_loops_trivial b p). Defined.

(** Lemma [lem:prop-utils]. *)
Section PropUtils.

  Definition False_isProp : isProp False := fun a => match a with end.

  Definition True_isProp : isProp True
    := fun a b => match a, b with triv, triv => refl end.

  Definition Pi_isProp `{Funext} {A : Type} {R : A -> Type}
    (h : forall a, isProp (R a)) : isProp (forall a, R a)
    := fun p q => ptw_inv (fun a => h a (p a) (q a)).

  Definition fun_isProp `{Funext} {A P : Type} (h : isProp P)
    : isProp (A -> P)
    := Pi_isProp (fun _ => h).

  Definition Sigma_isProp {A : Type} {R : A -> Type} (hA : isProp A)
    (hR : forall a, isProp (R a)) : isProp {a : A & R a}.
  Proof.
    intros [a1 r1] [a2 r2].
    pose (u := hA a1 a2).
    exact (pathpair u (trp (fun T : Type => T) (po u r1 r2)^ (hR _ _ _))).
  Defined.

  Definition prod_isProp {P Q : Type} (hP : isProp P) (hQ : isProp Q)
    : isProp (P × Q)
    := Sigma_isProp hP (fun _ => hQ).

  Definition neg_isProp `{Funext} (A : Type) : isProp (¬ A)
    := fun_isProp False_isProp.

  Definition lem_isProp `{Funext} {P : Type} (hP : isProp P)
    : isProp (P ⨿ ¬ P).
  Proof.
    intros [p|np] [q|nq].
    - exact (ap inl (hP p q)).
    - destruct (nq p).
    - destruct (np q).
    - exact (ap inr (neg_isProp P np nq)).
  Defined.

End PropUtils.

(** [𝟙 ⨿ 𝟙] is not a proposition. *)
Definition True_plus_True_not_prop : ¬ isProp (True ⨿ True)
  := fun h => inl_ne_inr triv triv (h (inl triv) (inr triv)).

(** Lemma [lem:level-n-utils], which the book states without proof.  We
    prove it by comparing [is_ntype] with Coq-HoTT's [IsTrunc]. *)
Fixpoint tr_nat (n : ℕ) : trunc_index
  := match n with O => minus_two.+2 | S n => (tr_nat n).+1 end.

Definition isProp_IsHProp {P : Type} : isProp P -> IsHProp P
  := hprop_allpath P.

Definition IsHProp_isProp {P : Type} `{IsHProp P} : isProp P
  := path_ishprop.

Definition ntype_IsTrunc (n : ℕ) {X : Type}
  : is_ntype n X -> IsTrunc (tr_nat n) X.
Proof.
  revert X. induction n as [|n IH]; intros X h; apply istrunc_S; intros x y.
  - exact (isProp_IsHProp (h x y)).
  - exact (IH _ (h x y)).
Defined.

Definition IsTrunc_ntype (n : ℕ) {X : Type}
  : IsTrunc (tr_nat n) X -> is_ntype n X.
Proof.
  revert X. induction n as [|n IH]; intros X h x y.
  - exact IsHProp_isProp.
  - exact (IH _ _).
Defined.

Section LevelNUtils.

  Context `{Funext} (n : ℕ).

  Definition Pi_ntype {A : Type} {Z : A -> Type}
    (h : forall a, is_ntype n (Z a)) : is_ntype n (forall a, Z a).
  Proof.
    pose proof (fun a => ntype_IsTrunc n (h a)).
    apply IsTrunc_ntype. exact _.
  Defined.

  Definition fun_ntype {A X : Type} (h : is_ntype n X) : is_ntype n (A -> X)
    := Pi_ntype (fun _ => h).

  Definition Sigma_ntype {A : Type} {Z : A -> Type} (hA : is_ntype n A)
    (h : forall a, is_ntype n (Z a)) : is_ntype n {a : A & Z a}.
  Proof.
    pose proof (ntype_IsTrunc n hA).
    pose proof (fun a => ntype_IsTrunc n (h a)).
    apply IsTrunc_ntype. exact _.
  Defined.

  Definition prod_ntype {X Y : Type} (hX : is_ntype n X) (hY : is_ntype n Y)
    : is_ntype n (X × Y)
    := Sigma_ntype hX (fun _ => hY).

End LevelNUtils.

(** Lemma [lem:isX-is-prop]. *)
Section IsXIsProp.

  Context `{Funext}.

  (** [isContr(A)] is a proposition, following the proof in the book. *)
  Definition isContr_isProp (A : Type) : isProp (isContr A).
  Proof.
    intros [a f] [b g].
    assert (hA : isProp A) by exact (fun x y => f y ⋅ (f x)⁻¹).
    pose (e := f b).
    exact (pathpair e (trp (fun T : Type => T) (po e f g)^
                         (Pi_isProp (fun y => prop_is_set hA b y) _ _))).
  Defined.

  (** Exercise [xca:isX-is-prop]. *)
  Definition isProp_isProp (A : Type) : isProp (isProp A).
  Proof.
    intros f g.
    apply ptw_inv. intro a. apply ptw_inv. intro b.
    exact (prop_is_set f a b _ _).
  Defined.

  Definition isSet_isProp (A : Type) : isProp (isSet A)
    := Pi_isProp (fun x => Pi_isProp (fun y => isProp_isProp (x = y))).

  Definition isGrpd_isProp (A : Type) : isProp (isGrpd A)
    := Pi_isProp (fun x => Pi_isProp (fun y => isSet_isProp (x = y))).

  Definition ntype_isProp (n : ℕ) : forall A : Type, isProp (is_ntype n A).
  Proof.
    induction n as [|n IH]; intro A.
    - exact (isSet_isProp A).
    - exact (Pi_isProp (fun x => Pi_isProp (fun y => IH (x = y)))).
  Defined.

  Definition isEquiv_isProp {X Y : Type} (f : X -> Y) : isProp (isEquiv f)
    := Pi_isProp (fun y => isContr_isProp (fiber f y)).

End IsXIsProp.

(** Exercise [xca:prop-contractible=]. *)
Definition isProp_iff_paths_contr (P : Type)
  : (isProp P -> forall p q : P, isContr (p = q))
    * ((forall p q : P, isContr (p = q)) -> isProp P).
Proof.
  split.
  - intros h p q. exact (h p q; fun r => prop_is_set h p q (h p q) r).
  - intros c p q. exact (fst (c p q)).
Defined.

(** Remark [rem:diagram] introduces diagrams as notation for identity
    types (e.g. [g ∘ p = q ∘ f]); it has no further formal content. *)

(** ** Univalence from Coq-HoTT

    The book's univalence axiom follows from Coq-HoTT's [Univalence]:
    [idtoeqv] is homotopic to the composite of the library's
    [equiv_path] with the equivalence [(X <~> Y) ≃ (X ≃ Y)]. *)

Definition isEquiv_homotopic {X Y : Type} (f g : X -> Y)
  (h : forall x, f x = g x) (t : isEquiv f) : isEquiv g
  := isEquiv_of_IsEquiv g (H := isequiv_homotopic f (H := IsEquiv_of_isEquiv t) h).

Definition Eqv_of_Equiv_isEquiv `{Funext} (X Y : Type)
  : isEquiv (@Eqv_of_Equiv X Y).
Proof.
  refine (iso_to_isEquiv _ (fun e => Build_Equiv _ _ (fst e) (IsEquiv_of_isEquiv (snd e)))
            _ _).
  - intro e. apply path_equiv. exact refl.
  - intro e. apply path_Eqv. exact refl.
Defined.

Instance UnivalenceUF_from_HoTT `{Univalence} : UnivalenceUF.
Proof.
  intros X Y.
  refine (isEquiv_homotopic (comp Eqv_of_Equiv (equiv_path X Y)) _ _
            (comp_isEquiv (isEquiv_of_IsEquiv (equiv_path X Y))
                       (Eqv_of_Equiv_isEquiv X Y))).
  intro p. destruct p. apply path_Eqv. exact refl.
Defined.

(** ** Bridges to Coq-HoTT used in the rest of the chapter

    These conversions between the book's notions and the library's are
    needed from 2.16 on; the other bridges are collected in [Bridge.v]. *)

Definition Eqv_of_props {P Q : Type} (hP : isProp P) (hQ : isProp Q)
  (f : P -> Q) (g : Q -> P) : P ≃ Q
  := mkEqv f g (fun p => hP _ _) (fun q => hQ _ _).

(** Fibers: [y = f x] versus [f x = y]. *)
Definition fiber_hfiber {X Y : Type} (f : X -> Y) (y : Y)
  : fiber f y ≃ hfiber f y
  := mkEqv (fun w : fiber f y => (fst w; (snd w)^) : hfiber f y)
           (fun w : hfiber f y => (pr1 w; (pr2 w)^) : fiber f y)
           (fun w => ap (fun r => (fst w; r) : fiber f y) (inv_V (snd w)))
           (fun w => ap (fun r => (pr1 w; r) : hfiber f y) (inv_V (pr2 w))).

Definition isSet_IsHSet {X : Type} : isSet X -> IsHSet X := ntype_IsTrunc 0.
Definition IsHSet_isSet {X : Type} : IsHSet X -> isSet X := IsTrunc_ntype 0.

Definition Equiv_of_Eqv {X Y : Type} (e : X ≃ Y) : X <~> Y
  := Build_Equiv X Y (fst e) (IsEquiv_of_isEquiv (snd e)).

(** * Part 4: Sections 2.16 - 2.18

    ** Summary of this formalization

    Sections 2.16 - 2.18 are formalized in this file, which builds on
    [IntroUF.v] - [IntroUF3.v] and [Bridge.v].  It compiles, with nothing
    admitted.  [Print Assumptions]: results using propositional
    truncation depend on Coq-HoTT's [istrunc_truncation] (the axiom that
    implements the truncation's identification constructor); [Funext] is
    used only where function extensionality is needed; and [Univalence]
    only for the results about identifications in [Prop] and [Set]
    ([same_component_props], [Bool_SetU_not_isInj], [xca:lem-prop] and
    [xca:lem-prop-sizing]) and for [xca:unique-fact-image].

    Book notions defined from Coq-HoTT notions: the propositional
    truncation [‖T‖ :≡ ptrunc T :≡ Trunc (-1) T] with [trunc :≡ tr]; its
    induction principle [ptrunc_ind] is the library's [Trunc_ind], so
    [f(|t|) ≡ g(t)] holds by definition.  Own definitions: [nonempty],
    [PropU] and [SetU] (the book's [Prop] and [Set], which are reserved
    words in Rocq), disjunction [∨], [Ex] (the book's [∃]), [ExUnique],
    [component], [isConn], [isSurj], [isSplitSurj], [isInj], [im],
    [isDecidable], [LEM], [DNE] and [PropResizing].  The library's
    surjections and embeddings use fibers with [f x = y], so [isSurj] and
    [isInj] are defined with the book's convention [y = f x].

    2.16 Propositional truncation and logic
    - [‖T‖] is a proposition; induction and recursion principles; the
      universal property [(‖T‖ → P) ≃ (T → P)] for propositions [P].
    - Exercises: [∃_{t:T} (x = |t|)] for [x : ‖T‖]; [P ≃ ‖P‖] for
      propositions [P].
    - Connected components and connectedness; [∅] is not connected.
    - Exercise [xca:component-connected]: components are connected, and
      elements in the same component have the same propositional
      properties ([P x = P y] in [Prop], via univalence).
    - Exercises [xca:connected-trivia], [xca:connected-trivia-1] and
      [xca:connected-trivia-2].

    2.17 More on equivalences; surjections and injections
    - Surjections (and split surjections with their sections) and
      injections; exercise [xca:inj-sets], including a function
      [True → Set] that is not injective (it maps to [Bool], and uses
      [refl ≠ swap] from 2.13).
    - [lem:inj+surj], [cor:inj+connected] and
      [lem:whenisbasespaceconnected].
    - [con:fib-vs-path], following the book's chain of equivalences, and
      [lem:inj-ap].
    - [cor:fib-vs-path]: parts 1 and 2 are proved for any property [Q] of
      types invariant under equivalence, and instantiated with [is_ntype n]
      ([n ≥ 0]; [is_ntype (succ n) X] is by definition
      [∏_{x,y} is_ntype n (x = y)]), [isProp] ([n = -1]) and [isContr]
      ([n = -2]); parts 3 and 4 for connected types.
    - Exercise [xca:sum-equivalences].
    - The image [im f] and the factorization [f = i ∘ p], which commutes
      by definition, with [p] surjective and [i] injective; exercises
      [xca:prop-image-is-set] and [xca:all-prop-image].
    - Exercise [xca:unique-fact-image], second part: the type [ImFact]
      of image factorizations is contractible ([ImFact_isContr]), with
      center the image factorization.  It suffices that [ImFact] is a
      proposition.  Following a hint by the author, two factorizations
      [(C,g,h)] and [(C',g',h')] give [e : C → C'] with [e(c)] in the
      fiber of [h'] at [h(c)]: that fiber is a proposition, so we may
      assume [a : A] with [c = g(a)] and take [g'(a)] ([fact_map]).  The
      same construction in the other direction gives an inverse, since
      the fibers of [h] and [h'] are propositions ([fact_Eqv]).  To avoid
      transporting the identification [f = h ∘ g] along [ua(e)], the
      6-tuples are reordered as [(C, h, isInj h, (g, f = h ∘ g), isSurj g)]
      ([ImFact_reorder]).  For injective [h], the type
      [∑_g (f = h ∘ g)] is a proposition ([lift_isProp]), being a retract
      of [∏_a h⁻¹(f(a))].  So only [(C, h)] has to be identified, by
      induction on the path [ua(e)] ([fact_path]).
      NOTE for the book text: the author's hint, together with the
      observation that [∑_g (f = h ∘ g)] is a proposition when [h] is
      injective, could be added to the exercise.

    2.18 Decidability, excluded middle and propositional resizing
    - Decidable propositions, LEM, double-negation elimination; LEM
      implies DNE, and exercise [xca:dne-lem] (DNE implies LEM).
    - Exercise [xca:lem-prop]: LEM holds iff [(yes = _) : Bool → Prop] is
      an equivalence.
    - Propositional resizing for universes [u < v], and exercise
      [xca:lem-prop-sizing]: LEM in the larger universe implies it.

    Things that differ from the text
    - The notation [‖T‖] is used only in comments: a notation whose
      opening and closing delimiters coincide cannot be parsed reliably,
      so the code writes [ptrunc T].
    - [∃] is written [Ex], since [exists] is a keyword.

    ** Conventions

    Continuation of [IntroUF.v], [IntroUF2.v], [IntroUF3.v] and
    [Bridge.v], with the same conventions: path composition
    [q ⋅ p :≡ p ∙ q], fibers with [y = f x], and notions that occur
    definitionally in Coq-HoTT defined from the library notion and used
    under the book's name.  Results that need univalence assume
    Coq-HoTT's [Univalence], from which the book's [UnivalenceUF] and
    function extensionality are derived. *)

(** ** Preliminaries

    Contractibility, propositions and [n]-types are invariant under
    equivalence. *)

Definition isContr_Eqv {X Y : Type} (e : X ≃ Y) (c : isContr X) : isContr Y
  := (fst e (fst c);
      fun y => eqinv_r (snd e) y ⋅ ap (fst e) (snd c (eqinv (snd e) y))).

Definition isProp_Eqv {X Y : Type} (e : X ≃ Y) (h : isProp X) : isProp Y
  := fun y y' => eqinv_r (snd e) y' ⋅ ap (fst e) (h _ _) ⋅ (eqinv_r (snd e) y)⁻¹.

Definition is_ntype_Eqv (n : ℕ) {X Y : Type} (e : X ≃ Y) (h : is_ntype n X)
  : is_ntype n Y
  := IsTrunc_ntype n
       (@istrunc_equiv_istrunc X Y (Equiv_of_Eqv e) _ (ntype_IsTrunc n h)).

(** A contractible type is a proposition, and an inhabited proposition is
    contractible. *)
Definition isContr_isProp' {X : Type} (c : isContr X) : isProp X
  := isContr_center c.

Definition isProp_inhabited_isContr {X : Type} (h : isProp X) (x : X)
  : isContr X
  := (x; h x).

(** Identity types: the equivalences [(s = w) ≃ (t = w)] and
    [(w = s) ≃ (w = t)] for [e : s = t], and symmetry. *)
Definition eq_l_eqv {X : Type} {s t w : X} (e : s = t) : (s = w) ≃ (t = w).
Proof. destruct e. exact (idEqv _). Defined.

Definition eq_r_eqv {X : Type} {s t w : X} (e : s = t) : (w = s) ≃ (w = t).
Proof. destruct e. exact (idEqv _). Defined.

Definition symm_eqv {X : Type} {x y : X} : (x = y) ≃ (y = x)
  := mkEqv symm symm symm_symm symm_symm.

(** ** 2.16 Propositional truncation and logic *)

(** Definition [def:prop-trunc]: the propositional truncation [‖T‖] is the
    library's [Trunc (-1) T], with element constructor [trunc :≡ tr], written
    [|t|] in the book.  Its induction principle satisfies
    [f(|t|) ≡ g(t)] by definition. *)
Definition ptrunc (T : Type) : Type := Trunc (-1) T.

Definition trunc {T : Type} : T -> (ptrunc T) := tr.

(** The identification constructor: [‖T‖] is a proposition. *)
Definition ptrunc_isProp {T : Type} : isProp (ptrunc T)
  := @IsHProp_isProp _ (istrunc_truncation (-1) T).

(** The induction principle, for families of propositions. *)
Definition ptrunc_ind {T : Type} (P : (ptrunc T) -> Type)
  (hP : forall x, isProp (P x)) (g : forall t, P (trunc t))
  : forall x, P x
  := Trunc_ind P (Pt := fun x => isProp_IsHProp (hP x)) g.

Definition ptrunc_ind_trunc {T : Type} (P : (ptrunc T) -> Type) hP g (t : T)
  : ptrunc_ind P hP g (trunc t) = g t := refl.

(** The recursion principle, for a constant family. *)
Definition ptrunc_rec {T P : Type} (hP : isProp P) (g : T -> P) : (ptrunc T) -> P
  := ptrunc_ind (fun _ => P) (fun _ => hP) g.

(** The universal property of propositional truncation:
    [(‖T‖ → P) ≃ (T → P)] by precomposition with [|_|]. *)
Definition ptrunc_univ_prop `{Funext} (T : Type) {P : Type} (hP : isProp P)
  : ((ptrunc T) -> P) ≃ (T -> P)
  := mkEqv (fun h => h ∘ trunc) (ptrunc_rec hP)
       (fun h => ptw_inv (ptrunc_ind (fun x => ptrunc_rec hP (h ∘ trunc) x = h x)
                            (fun x => prop_is_set hP _ _) (fun t => refl)))
       (fun g => refl).

(** Definition [def:non-empty]. *)
Definition nonempty (T : Type) : Type := (ptrunc T).

(** The type [Prop_U :≡ ∑_{X:U} isProp(X)].  ([Prop] is a reserved word
    in Rocq, hence the name [PropU].) *)
Definition PropU : Type := {X : Type & isProp X}.

Definition ptrunc_PropU (T : Type) : PropU := ((ptrunc T); ptrunc_isProp).

(** Disjunction, existence, and unique existence. *)
Definition disj (P Q : Type) : Type := (ptrunc (P ⨿ Q)).
Notation "P ∨ Q" := (disj P Q) (at level 85, right associativity) : uf_scope.

Definition Ex {X : Type} (P : X -> Type) : Type := (ptrunc ({x : X & P x})).

Definition ExUnique {X : Type} (P : X -> Type) : Type
  := isContr {x : X & P x}.

(** Exercise: for [x : ‖T‖], [∃_{t:T} (x = |t|)]. *)
Definition ptrunc_exists_trunc {T : Type} (x : (ptrunc T))
  : Ex (fun t : T => x = trunc t)
  := ptrunc_ind (fun x => Ex (fun t : T => x = trunc t))
       (fun _ => ptrunc_isProp) (fun t => trunc (t; refl)) x.

(** Exercise [xca:prop-trivia-1]: [P ≃ ‖P‖] for a proposition [P]. *)
Definition prop_ptrunc_eqv {P : Type} (h : isProp P) : P ≃ (ptrunc (P))
  := Eqv_of_props h ptrunc_isProp trunc (ptrunc_rec h idmap).

(** Definition [def:connected]: connected components and connectedness. *)
Definition component (A : Type) (a : A) : Type := {x : A & (ptrunc (a = x))}.

Definition isConn (A : Type) : Type := (ptrunc (A)) × (forall x y : A, (ptrunc (x = y))).

(** The empty type is not connected. *)
Definition False_not_isConn : ¬ isConn False
  := fun c => ptrunc_rec False_isProp idmap (fst c).

(** Exercise [xca:component-connected], first part. *)
Definition component_isConn {A : Type} (a : A) : isConn (component A a).
Proof.
  refine (trunc ((a; trunc refl) : component A a); _).
  intros [x p] [y q].
  revert p.
  refine (ptrunc_ind (fun p => (ptrunc (((x; p) : component A a) = (y; q))))
            (fun _ => ptrunc_isProp) _).
  intro p0. revert q.
  refine (ptrunc_ind (fun q => (ptrunc (((x; trunc p0) : component A a) = (y; q))))
            (fun _ => ptrunc_isProp) _).
  intro q0.
  exact (trunc (pathpair (q0 ⋅ p0⁻¹) (ptrunc_isProp _ _))).
Defined.

(** Identifications in [Prop_U] come from logical equivalences, using
    univalence. *)
Definition path_PropU `{Univalence} {P Q : PropU}
  (f : fst P -> fst Q) (g : fst Q -> fst P) : P = Q
  := pathpair (etop (Eqv_of_props (snd P) (snd Q) f g))
       (isProp_isProp (fst Q) _ _).

(** Exercise [xca:component-connected], second part: elements in the same
    component have the same propositional properties. *)
Definition same_component_props `{Univalence} {A : Type} (P : A -> PropU)
  {x y : A} (h : ptrunc (x = y)) : P x = P y.
Proof.
  pose (fg := ptrunc_rec
                (prod_isProp (fun_isProp (snd (P y))) (fun_isProp (snd (P x))))
                (fun e => (trp (fun z => fst (P z)) e;
                           trp (fun z => fst (P z)) e⁻¹)) h).
  exact (path_PropU (fst fg) (snd fg)).
Defined.

(** Exercise [xca:connected-trivia]. *)
Definition conn_loops_prop_isContr {A : Type} (c : isConn A)
  (h : forall a : A, isProp (a = a)) : isContr A.
Proof.
  assert (hp : forall x y : A, isProp (x = y)).
  { intros x y p q. destruct q. exact (h x p refl). }
  assert (hA : isProp A).
  { intros x y. exact (ptrunc_rec (hp x y) idmap (snd c x y)). }
  exact (isProp_inhabited_isContr hA (ptrunc_rec hA idmap (fst c))).
Defined.

Definition conn_set_isContr {A : Type} (c : isConn A) (s : isSet A)
  : isContr A
  := conn_loops_prop_isContr c (fun a => s a a).

(** Exercise [xca:connected-trivia-1]. *)
Definition Sigma_isConn {A : Type} {B : A -> Type} (cA : isConn A)
  (cB : forall x, isConn (B x)) : isConn {x : A & B x}.
Proof.
  refine (ptrunc_rec ptrunc_isProp
            (fun a => ptrunc_rec ptrunc_isProp (fun b => trunc (a; b))
                        (fst (cB a))) (fst cA); _).
  intros [a b] [a' b'].
  refine (ptrunc_rec ptrunc_isProp _ (snd cA a a')). intro p.
  refine (ptrunc_rec ptrunc_isProp _ (snd (cB a') (trp B p b) b')). intro q.
  exact (trunc (pathpair p q)).
Defined.

(** Exercise [xca:connected-trivia-2]. *)
Definition Sigma_ptrunc_isConn {A : Type} {B : A -> Type}
  (c : isConn {a : A & B a}) : isConn {a : A & ptrunc (B a)}.
Proof.
  pose (t := tot (fun a => @trunc (B a))).
  refine (ptrunc_rec ptrunc_isProp (fun w => trunc (t w)) (fst c); _).
  intros [a u] [a' u'].
  revert u.
  refine (ptrunc_ind
            (fun u => ptrunc (((a; u) : {a : A & ptrunc (B a)}) = (a'; u')))
            (fun _ => ptrunc_isProp) _).
  intro b. revert u'.
  refine (ptrunc_ind
            (fun u' => ptrunc (((a; trunc b) : {a : A & ptrunc (B a)}) = (a'; u')))
            (fun _ => ptrunc_isProp) _).
  intro b'.
  exact (ptrunc_rec ptrunc_isProp (fun r => trunc (ap t r)) (snd c (a; b) (a'; b'))).
Defined.

(** Definition [def:merely]: merely constructing an element of [T] means
    constructing an element of [‖T‖]. *)

(** ** 2.17 More on equivalences; surjections and injections *)

(** Definition [def:surjection]. *)
Definition isSurj {A B : Type} (f : A -> B) : Type
  := forall b : B, Ex (fun a : A => b = f a).

(** Footnote: split surjections, and their sections. *)
Definition isSplitSurj {A B : Type} (f : A -> B) : Type
  := forall b : B, fiber f b.

Definition splitSurj_section `{Funext} {A B : Type} {f : A -> B}
  (s : isSplitSurj f)
  : {g : B -> A & f ∘ g = id B}
  := ((fun b => fst (s b)); ptw_inv (fun b => (snd (s b))⁻¹)).

(** Definition [def:injection]. *)
Definition isInj {A B : Type} (f : A -> B) : Type
  := forall b : B, isProp (fiber f b).

(** Exercise [xca:inj-sets]. *)
Definition isInj_cancel {A B : Type} {f : A -> B} (j : isInj f)
  : forall a a' : A, f a = f a' -> a = a'
  := fun a a' e => ap fst (j (f a') (a; e⁻¹) (a'; refl)).

Definition cancel_isInj {A B : Type} (sB : isSet B) {f : A -> B}
  (c : forall a a' : A, f a = f a' -> a = a') : isInj f.
Proof.
  intros b [a p] [a' p'].
  exact (pathpair (c a a' (p' ⋅ p⁻¹)) (sB _ _ _ _)).
Defined.

(** The type [Set_U :≡ ∑_{X:U} isSet(X)] ([Set] is reserved in Rocq). *)
Definition SetU : Type := {X : Type & isSet X}.

(** A function [True → Set] that is not injective. *)
Definition Bool_SetU : True -> SetU := fun _ => (Bool; isSet_bool).

Definition Bool_SetU_not_isInj `{Univalence} : ¬ isInj Bool_SetU.
Proof.
  intro j.
  pose (f := Bool_SetU).
  pose (g := fun w : fiber f (f triv) =>
               match fst w as t return (f triv = f t) -> (f triv = f triv) with
               | triv => idmap
               end (snd w)).
  pose (e2 := pathpair swap (isSet_isProp Bool _ _) : f triv = f triv).
  pose (r := ap g (j (f triv) (triv; refl) (triv; e2)) : refl = e2).
  apply refl_ne_swap.
  exact (ap_fst_pathpair swap _ ⋅ ap (ap fst) r).
Defined.

(** Lemma [lem:inj+surj]. *)
Definition isEquiv_isInj {A B : Type} {f : A -> B} (t : isEquiv f) : isInj f
  := fun b => isContr_isProp' (t b).

Definition isEquiv_isSurj {A B : Type} {f : A -> B} (t : isEquiv f)
  : isSurj f
  := fun b => trunc (fst (t b)).

Definition inj_surj_isEquiv `{Funext} {A B : Type} {f : A -> B}
  (j : isInj f) (s : isSurj f) : isEquiv f
  := fun b => ptrunc_rec (isContr_isProp _)
                (fun w => isProp_inhabited_isContr (j b) w) (s b).

(** Corollary [cor:inj+connected]. *)
Definition inj_conn_isEquiv `{Funext} {A B : Type} {f : A -> B}
  (nA : (ptrunc (A))) (cB : isConn B) (j : isInj f) : isEquiv f.
Proof.
  apply (inj_surj_isEquiv j). intro b.
  refine (ptrunc_rec ptrunc_isProp _ nA). intro a.
  exact (ptrunc_rec ptrunc_isProp (fun p => trunc (a; p)) (snd cB b (f a))).
Defined.

(** Lemma [lem:whenisbasespaceconnected]. *)
Definition surj_isConn {X Y : Type} {f : X -> Y} (s : isSurj f)
  (cX : isConn X) : isConn Y.
Proof.
  refine (ptrunc_rec ptrunc_isProp (fun x => trunc (f x)) (fst cX); _).
  intros y y'.
  refine (ptrunc_rec ptrunc_isProp _ (s y)). intros [x p].
  refine (ptrunc_rec ptrunc_isProp _ (s y')). intros [x' p'].
  refine (ptrunc_rec ptrunc_isProp _ (snd cX x x')). intro q.
  exact (trunc ((p'⁻¹ ⋅ ap f q) ⋅ p)).
Defined.

(** Construction [con:fib-vs-path]:
    [(z = z') ≃ ap_f⁻¹(snd(z') · snd(z)⁻¹)], following the chain of
    equivalences in the book. *)
Definition trp_fiber_path {A B : Type} (f : A -> B) {b : B} {a a' : A}
  (q : a = a') (p : b = f a)
  : trp (fun x => b = f x) q p = ap f q ⋅ p
  := match q with refl => refl end.

Definition cancel_eqv {X : Type} {b c d : X} (r : c = d) (p : b = c)
  (p' : b = d) : (r ⋅ p = p') ≃ (p' ⋅ p⁻¹ = r).
Proof.
  refine (Eqv_comp _ symm_eqv).
  destruct p.
  exact (Eqv_comp (eq_l_eqv (trans_1p r)) (eq_r_eqv (trans_1p p')⁻¹)).
Defined.

Definition fib_vs_path {A B : Type} (f : A -> B) {b : B} (z z' : fiber f b)
  : (z = z') ≃ fiber (ap f) (snd z' ⋅ (snd z)⁻¹).
Proof.
  destruct z as [a p], z' as [a' p'].
  refine (Eqv_comp (Eqv_inv (path_sigma_eqv (Y := fun x => b = f x))) _).
  pose (E := fun q : a = a' =>
               Eqv_comp (eq_l_eqv (trp_fiber_path f q p)) (cancel_eqv (ap f q) p p')).
  exact (tot (fun q => fst (E q)); tot_isEquiv _ (fun q => snd (E q))).
Defined.

(** Lemma [lem:inj-ap]. *)
Definition isInj_ap_isEquiv {A B : Type} {f : A -> B} (j : isInj f)
  : forall a a' : A, isEquiv (@ap A B f a a').
Proof.
  intros a a' r.
  pose (z := (a; refl) : fiber f (f a)).
  pose (z' := (a'; r) : fiber f (f a)).
  pose (c := Overture.fst (isProp_iff_paths_contr _) (j (f a)) z z').
  exact (trp (fun s => isContr (fiber (ap f) s)) (trans_1p r)
           (isContr_Eqv (fib_vs_path f z z') c)).
Defined.

Definition ap_isEquiv_isInj {A B : Type} {f : A -> B}
  (h : forall a a' : A, isEquiv (@ap A B f a a')) : isInj f
  := fun b z z' => eqinv (snd (fib_vs_path f z z'))
                     (fst (h (fst z) (fst z') (snd z' ⋅ (snd z)⁻¹))).

(** Corollary [cor:fib-vs-path].  We state the first two parts for any
    property [Q] of types that is invariant under equivalence; the book's
    statements are the instances [Q :≡ is_ntype n] (for [n ≥ 0]), and
    also [Q :≡ isProp] ([n = -1]) and [Q :≡ isContr] ([n = -2], which is
    [lem:inj-ap]).  Note that [is_ntype (succ n) X] is by definition
    [∏_{x,y:X} is_ntype n (x = y)]. *)
Section FibVsPath.

  Context {A B : Type} (f : A -> B) (Q : Type -> Type)
    (Qinv : forall X Y : Type, X ≃ Y -> Q X -> Q Y).

  (** Part [set-fib-vs-path]. *)
  Definition fibers_paths_Q
    : (forall (b : B) (z z' : fiber f b), Q (z = z'))
      -> forall (a a' : A) (r : f a = f a'), Q (fiber (ap f) r)
    := fun h a a' r =>
         trp (fun s => Q (fiber (ap f) s)) (trans_1p r)
           (Qinv _ _ (fib_vs_path f (a; refl) (a'; r)) (h (f a) _ _)).

  Definition Q_paths_fibers
    : (forall (a a' : A) (r : f a = f a'), Q (fiber (ap f) r))
      -> forall (b : B) (z z' : fiber f b), Q (z = z')
    := fun h b z z' => Qinv _ _ (Eqv_inv (fib_vs_path f z z')) (h _ _ _).

  (** Part [set-fib-vs-path-point], for [Q] proposition-valued. *)
  Definition Q_paths_fibers_point `{Funext} (Qprop : forall X, isProp (Q X))
    (cA : isConn A) (a : A)
    : (forall r : f a = f a, Q (fiber (@ap A B f a a) r))
      -> forall (b : B) (z z' : fiber f b), Q (z = z').
  Proof.
    intro h. apply Q_paths_fibers. intros a1 a2.
    refine (ptrunc_rec (Pi_isProp (fun _ => Qprop _)) _ (snd cA a a1)). intro p1.
    refine (ptrunc_rec (Pi_isProp (fun _ => Qprop _)) _ (snd cA a a2)). intro p2.
    destruct p1, p2. exact h.
  Defined.

End FibVsPath.

Definition isContr_Qinv : forall X Y : Type, X ≃ Y -> isContr X -> isContr Y
  := fun X Y => isContr_Eqv.

Definition isProp_Qinv : forall X Y : Type, X ≃ Y -> isProp X -> isProp Y
  := fun X Y => isProp_Eqv.

Definition is_ntype_Qinv (n : ℕ)
  : forall X Y : Type, X ≃ Y -> is_ntype n X -> is_ntype n Y
  := fun X Y => is_ntype_Eqv n.

(** Part [set-fib-vs-path] for [n]-types, [n ≥ 0]: all fibers of [f] are
    [(n+1)]-types iff all fibers of the maps [ap f] are [n]-types. *)
Definition fibers_ntype_iff {A B : Type} (f : A -> B) (n : ℕ)
  : ((forall b : B, is_ntype (succ n) (fiber f b))
      -> forall (a a' : A) (r : f a = f a'), is_ntype n (fiber (ap f) r))
    × ((forall (a a' : A) (r : f a = f a'), is_ntype n (fiber (ap f) r))
      -> forall b : B, is_ntype (succ n) (fiber f b))
  := (fibers_paths_Q f (is_ntype n) (is_ntype_Qinv n);
      Q_paths_fibers f (is_ntype n) (is_ntype_Qinv n)).

(** Part [conn-fib-vs-path]. *)
Definition conn_isEquiv_iff `{Funext} {A B : Type} (f : A -> B)
  (cA : isConn A) (cB : isConn B)
  : (isEquiv f -> forall a a' : A, isEquiv (@ap A B f a a'))
    × ((forall a a' : A, isEquiv (@ap A B f a a')) -> isEquiv f)
  := (fun t => isInj_ap_isEquiv (isEquiv_isInj t);
      fun h => inj_conn_isEquiv (fst cA) cB (ap_isEquiv_isInj h)).

(** Part [conn-fib-vs-path-point]. *)
Definition conn_isEquiv_iff_point `{Funext} {A B : Type} (f : A -> B)
  (cA : isConn A) (cB : isConn B) (a : A)
  : (isEquiv f -> isEquiv (@ap A B f a a))
    × (isEquiv (@ap A B f a a) -> isEquiv f).
Proof.
  refine ((fun t => fst (conn_isEquiv_iff f cA cB) t a a); _).
  intro h.
  apply (inj_conn_isEquiv (fst cA) cB).
  intro b. apply (Overture.snd (isProp_iff_paths_contr _)).
  exact (Q_paths_fibers_point f isContr isContr_Qinv isContr_isProp cA a h b).
Defined.

(** Exercise [xca:sum-equivalences]. *)
Definition sum_equivalences {A B : Type} {F : A -> Type} {G : B -> Type}
  (f : A ≃ B) (g : forall a, F a ≃ G (fst f a))
  : {a : A & F a} ≃ {b : B & G b}
  := Eqv_comp (tot (fun a => fst (g a)); tot_isEquiv _ (fun a => snd (g a)))
       (Eqv_of_Equiv (equiv_functor_sigma_pb (Q := G) (Equiv_of_Eqv f))).

(** Definition [def:prop-image]: the (propositional) image. *)
Definition im {A B : Type} (f : A -> B) : Type
  := {y : B & Ex (fun x : A => y = f x)}.

(** Exercise [xca:unique-fact-image], first part: the factorization
    [f = i ∘ p], which commutes by definition, with [p] surjective and
    [i] injective. *)
Section ImageFactorization.

  Context {A B : Type} (f : A -> B).

  Definition im_p : A -> im f := fun x => (f x; trunc (x; refl)).

  Definition im_i : im f -> B := fst.

  Definition im_factor : f = im_i ∘ im_p := refl.

  Definition im_p_isSurj : isSurj im_p.
  Proof.
    intros [y u]. revert u.
    refine (ptrunc_ind
              (fun u => Ex (fun x : A => ((y; u) : im f) = im_p x))
              (fun _ => ptrunc_isProp) _).
    intros [x e].
    exact (trunc (x; pathpair e (ptrunc_isProp _ _))).
  Defined.

  Definition im_i_isInj : isInj im_i.
  Proof.
    intros b [[y u] e] [[y' u'] e'].
    change (b = y) in e. change (b = y') in e'.
    destruct e, e'.
    exact (ap (fun u0 => (((b; u0) : im f); refl) : fiber im_i b)
              (ptrunc_isProp u u')).
  Defined.

End ImageFactorization.

(** Exercise [xca:unique-fact-image], second part: the type of image
    factorizations is contractible. *)
Section ImageFactorizationUnique.

  Context `{Univalence} {A B : Type} (f : A -> B).

  (** The type of image factorizations of [f]. *)
  Definition ImFact : Type
    := {C : Type & {g : A -> C & {h : C -> B &
         (f = h ∘ g) × isSurj g × isInj h}}}.

  Definition im_fact : ImFact
    := (im f; (im_p f; (im_i f; ((refl; im_p_isSurj f); im_i_isInj f)))).

  Definition isSurj_isProp {X Y : Type} (g : X -> Y) : isProp (isSurj g)
    := Pi_isProp (fun _ => ptrunc_isProp).

  (** If [h] is injective, then [∑_{g : A → C} (f = h ∘ g)] is a
      proposition: it is a retract of [∏_{a:A} h⁻¹(f(a))]. *)
  Definition lift_isProp {C : Type} {h : C -> B} (j : isInj h)
    : isProp {g : A -> C & f = h ∘ g}.
  Proof.
    pose (s := fun w : {g : A -> C & f = h ∘ g} =>
                 (fun a => (fst w a; ptw (snd w) a)) : forall a, fiber h (f a)).
    pose (r := fun F : forall a, fiber h (f a) =>
                 ((fun a => fst (F a)); ptw_inv (fun a => snd (F a)))
                 : {g : A -> C & f = h ∘ g}).
    assert (rs : forall w, r (s w) = w).
    { intros [g φ]. exact (ap (fun φ' => (g; φ') : {g : A -> C & f = h ∘ g})
                              (eqinv_l (funext _ _) φ)). }
    intros w w'.
    exact ((rs w)^ @ ap r (Pi_isProp (fun a => j (f a)) (s w) (s w')) @ rs w').
  Defined.

  (** The factorizations, reordered: first [C] and the injection [h]. *)
  Definition FactRest (C : Type) (h : C -> B) : Type
    := {j : isInj h & {w : {g : A -> C & f = h ∘ g} & isSurj (fst w)}}.

  Definition FactRest_isProp (C : Type) (h : C -> B) : isProp (FactRest C h)
    := Sigma_isProp (Pi_isProp (fun _ => isProp_isProp _))
         (fun j => Sigma_isProp (lift_isProp j) (fun w => isSurj_isProp _)).

  Definition ImFact' : Type := {C : Type & {h : C -> B & FactRest C h}}.

  Definition ImFact_reorder : ImFact ≃ ImFact'.
  Proof.
    refine (mkEqv (fun x : ImFact => match x with (C; (g; (h; ((φ; s); j)))) =>
                              ((C; (h; (j; ((g; φ); s)))) : ImFact') end)
                  (fun x : ImFact' => match x with (C; (h; (j; ((g; φ); s)))) =>
                              ((C; (g; (h; ((φ; s); j)))) : ImFact) end) _ _).
    - intros [C [g [h [[φ s] j]]]]. exact refl.
    - intros [C [h [j [[g φ] s]]]]. exact refl.
  Defined.

  (** Following a hint by the author: for factorizations [(C,g,h)] and
      [(C',g',h')], define [e(c)] in the fiber of [h'] at [h(c)], which is
      a proposition; so we may assume [a : A] with [c = g(a)], and take
      [g'(a)]. *)
  Definition fact_map {C C' : Type} {h : C -> B} {h' : C' -> B}
    (r : FactRest C h) (r' : FactRest C' h') (c : C) : fiber h' (h c).
  Proof.
    destruct r as [j [[g φ] s]], r' as [j' [[g' φ'] s']].
    refine (ptrunc_rec (j' (h c)) _ (s c)). intros [a p].
    exact (g' a; ap h p @ (ptw φ a)^ @ ptw φ' a).
  Defined.

  Definition fact_Eqv {C C' : Type} {h : C -> B} {h' : C' -> B}
    (r : FactRest C h) (r' : FactRest C' h') : C ≃ C'.
  Proof.
    refine (mkEqv (fun c => fst (fact_map r r' c))
                  (fun c' => fst (fact_map r' r c')) _ _).
    - intro c. exact (ap fst (fst r (h c)
        (_; snd (fact_map r r' c) @ snd (fact_map r' r _)) (c; refl))).
    - intro c'. exact (ap fst (fst r' (h' c')
        (_; snd (fact_map r' r c') @ snd (fact_map r r' _)) (c'; refl))).
  Defined.

  Definition fact_path {C C' : Type} (p : C = C') {h : C -> B} {h' : C' -> B}
    (hh : forall c, h c = h' (ptoe p c)) (r : FactRest C h) (r' : FactRest C' h')
    : ((C; (h; r)) : ImFact') = (C'; (h'; r')).
  Proof.
    destruct p. destruct (ptw_inv hh : h = h').
    exact (ap (fun r0 => ((C; (h; r0)) : ImFact')) (FactRest_isProp C h r r')).
  Defined.

  Definition ImFact'_isProp : isProp ImFact'.
  Proof.
    intros [C [h r]] [C' [h' r']].
    pose (E := fact_Eqv r r').
    refine (fact_path (etop E) _ r r').
    intro c. exact (snd (fact_map r r' c) @ ap h' (ptw (ap fst (ptoe_etop E)) c)^).
  Defined.

  (** Exercise [xca:unique-fact-image], second part. *)
  Definition ImFact_isContr : isContr ImFact
    := isProp_inhabited_isContr
         (isProp_Eqv (Eqv_inv ImFact_reorder) ImFact'_isProp) im_fact.

End ImageFactorizationUnique.

(** Exercise [xca:prop-image-is-set]. *)
Definition im_isSet {A B : Type} (f : A -> B) (sB : isSet B) : isSet (im f).
Proof.
  apply IsHSet_isSet. pose proof (isSet_IsHSet sB).
  unfold im, Ex, ptrunc. exact _.
Defined.

(** Exercise [xca:all-prop-image]. *)
Definition all_prop_image {A B : Type} (f : A -> B) (P : B -> Type)
  (hP : forall b, isProp (P b))
  : ((forall z : im f, P (fst z)) -> forall a : A, P (f a))
    × ((forall a : A, P (f a)) -> forall z : im f, P (fst z))
  := (fun h a => h (im_p f a);
      fun k z => ptrunc_rec (hP (fst z))
                   (fun w => trp P (snd w)⁻¹ (k (fst w))) (snd z)).

(** ** 2.18 Decidability, excluded middle and propositional resizing *)

(** Definition [def:decidability]. *)
Definition isDecidable (P : Type) : Type := P ⨿ ¬ P.

(** Principle [pri:lem]: the Law of Excluded Middle. *)
Definition LEM : Type := forall P : Type, isProp P -> P ⨿ ¬ P.

(** Exercise [xca:lem-prop]: LEM holds iff [(yes = _) : Bool → Prop] is an
    equivalence. *)
Section LEMProp.

  Context `{Univalence}.

  Definition yes_eq : Bool -> PropU := fun b => ((yes = b); isSet_bool yes b).

  Definition LEM_yes_eq_isEquiv (lem : LEM) : isEquiv yes_eq.
  Proof.
    pose (g := fun P : PropU =>
                 match lem (fst P) (snd P) with inl _ => yes | inr _ => no end).
    refine (iso_to_isEquiv yes_eq g _ _).
    - intros []; unfold g; cbn.
      + destruct (lem (yes = yes) _) as [e|ne].
        * exact refl.
        * destruct (ne refl).
      + destruct (lem (yes = no) _) as [e|ne].
        * destruct (yes_ne_no e).
        * exact refl.
    - intro P. unfold g.
      destruct (lem (fst P) (snd P)) as [p|np].
      + exact (path_PropU (P := yes_eq yes) (fun _ => p) (fun _ => refl)).
      + exact (path_PropU (P := yes_eq no)
                 (fun e => match yes_ne_no e with end)
                 (fun p => match np p with end)).
  Defined.

  Definition yes_eq_isEquiv_LEM (t : isEquiv yes_eq) : LEM.
  Proof.
    intros P hP.
    generalize (eqinv_r t (P; hP)). generalize (eqinv t (P; hP)).
    intros b e.
    pose (e1 := ap fst e : (yes = b) = P).
    destruct b.
    - exact (inl (ptoe e1 refl)).
    - exact (inr (fun p => yes_ne_no (ptoe e1⁻¹ p))).
  Defined.

End LEMProp.

(** Proof by contradiction: LEM implies double-negation elimination. *)
Definition DNE : Type := forall P : Type, isProp P -> ¬ ¬ P -> P.

Definition LEM_DNE (lem : LEM) : DNE
  := fun P hP nnp => match lem P hP with
                     | inl p => p
                     | inr np => match nnp np with end
                     end.

(** Exercise [xca:dne-lem]: double-negation elimination implies LEM. *)
Definition DNE_LEM `{Funext} (dne : DNE) : LEM
  := fun P hP => dne (P ⨿ ¬ P) (lem_isProp hP)
                   (fun k => k (inr (fun p => k (inl p)))).

(** Principle [pri:prop-resizing]: for universes [U : U'], the map
    [(P ↦ P) : Prop_U → Prop_U'] is an equivalence. *)
Section Resizing.

  Universes u v.
  Constraint u < v.

  Definition lift_PropU : {X : Type@{u} & isProp X} -> {X : Type@{v} & isProp X}
    := fun P => exist (fun X : Type@{v} => isProp X) (fst P) (fun a b => snd P a b).

  Definition PropResizing : Type := isEquiv lift_PropU.

  (** [True] and [False] as propositions in [U]. *)
  Definition True_u : {X : Type@{u} & isProp X}
    := exist (fun X : Type@{u} => isProp X) True (fun a b => True_isProp a b).
  Definition False_u : {X : Type@{u} & isProp X}
    := exist (fun X : Type@{u} => isProp X) False (fun a b => False_isProp a b).

  (** Exercise [xca:lem-prop-sizing]: LEM (in [U']) implies propositional
      resizing. *)
  Definition LEM_PropResizing `{Univalence}
    (lem : forall P : Type@{v}, isProp P -> P ⨿ ¬ P) : PropResizing.
  Proof.
    pose (g := fun Q : {X : Type@{v} & isProp X} =>
                 match lem (fst Q) (snd Q) with
                 | inl _ => True_u
                 | inr _ => False_u
                 end).
    refine (iso_to_isEquiv lift_PropU g _ _).
    - intro P. unfold g; cbn.
      destruct (lem (fst P) (fun a b => snd P a b)) as [p|np].
      + exact (path_PropU (P := True_u) (fun _ => p) (fun _ => triv)).
      + exact (path_PropU (P := False_u)
                 (fun x => match x with end) (fun p => match np p with end)).
    - intro Q. unfold g.
      destruct (lem (fst Q) (snd Q)) as [q|nq].
      + exact (path_PropU (P := lift_PropU True_u) (fun _ => q) (fun _ => triv)).
      + exact (path_PropU (P := lift_PropU False_u)
                 (fun x => match x with end) (fun q => match nq q with end)).
  Defined.

End Resizing.

(** * Part 5: Sections 2.19 - 2.21

    ** Summary of this formalization

    Sections 2.19 - 2.21 are formalized in this file, which builds on
    [IntroUF.v] - [IntroUF4.v] and [Bridge.v].  It compiles, with nothing
    admitted.  [Print Assumptions]: [Funext] is used only where function
    extensionality is needed, [Univalence] only for the results that
    need it (smallness being a proposition, [Prop] being a set, subtypes
    versus injections, antisymmetry of inclusion, and pointed
    identifications versus pointed equivalences), and the truncation
    axiom only for the connected-component exercise.  [U_locSmall] uses
    the book's univalence class [UnivalenceUF] as a hypothesis.

    Book notions defined from Coq-HoTT notions: none are new here.  The
    library's pointed types ([pType]) are records with pointing paths
    [f(pt) = pt], whereas the book uses pairs and [pt = f(pt)], so pointed
    types, pointed maps and pointed equivalences are our own.  Hedberg's
    theorem is the library's [hset_decpaths].

    2.19 The replacement principle
    - Essentially and locally [U]-small types ([essSmall], [locSmall]);
      essential smallness is invariant under equivalence and implies
      local smallness; small types are essentially small; a reflexive
      relation [Eq_A] inducing equivalences shows local smallness.
    - Being essentially small is a proposition (by univalence).
    - Exercise: [U] is locally [U]-small, and locally small types are
      closed under products over a small type.
    - Remark: propositional resizing makes propositions essentially small
      and sets locally small.
    - The replacement principle as a definition [Replacement], and
      exercise [xca:comp-loc-small-ess-small].

    2.20 Predicates and subtypes
    - Decidable predicates and characteristic functions; exercise
      [xca:decidability].
    - [Sub(T)], the underlying type [T_P] ([carrier P]), and
      [lem:subtype-eq-=] (the first projection is an injection; the book
      uses [cor:contract-away], we show directly that its fibers are
      propositions).
    - [lem:Prop-in-Set] ([Prop] is a set), hence [Sub(T)] is a set.
    - Exercise [xca:subtype-univ-prop], via [xca:section-above-f].
    - [Inj(T)] and [lem:Sub(T)=Inj(T)] / exercise [xca:Sub(T)=Inj(T)]:
      [Sub(T) ≃ Inj(T)] for [T : U], by univalence.
    - [cor:subtype-same-level] for propositions and [n]-types, [n ≥ 0].
    - Exercise [xca:subsets-inclusion]: [⊆] is a proposition-valued
      partial order with least and greatest elements.
    - Decidable sets, and Hedberg's theorem.

    2.21 Pointed types
    - [U_* :≡ ∑_{A:U} A], [A_+], underlying types [utype X] (the book's
      [X_÷]), base points [pt X], pointed maps [X →* Y] as the fiber of
      [ev_{pt_X}] at [pt_Y], composition and pointed identities.
    - Exercises [xca:plusforgetadjoint] and [xca:freemaps].
    - Pointed equivalences [X ≃* Y], and exercise [xca:pointedequiv]:
      [(X = Y) ≃ (X ≃* Y)], by showing that [∑_Y (X ≃* Y)] is
      contractible (using univalence).
    - [con:identity-ptd-maps] ([ptw_*]), following the book's chain of
      equivalences, and exercise [xca:identity-ptd-maps] ([ptw_*] by
      induction).
    - Exercise [xca:filler-ptd-sum-of-fibers], with the equivalence
      [(∑_y f⁻¹(y)) ≃ X] constructed here.
    - Exercise [xca:ptd-equiv-inv]: the pointed inverse, and
      identifications of [f⁻¹ f] and [f f⁻¹] with the pointed identities.
      For the second we use the half-adjoint coherence ([eisadj])
      provided by Coq-HoTT for the inverse, as in Theorem 4.2.3 of the
      HoTT Book.

    Things that differ from the text
    - [Prop] and [Set] are reserved words in Rocq, hence [PropU], [SetU]
      (from [IntroUF4.v]); [T_P] is written [carrier P].
    - The closure properties of small types are investigated only for
      products (the book's example).

    ** Conventions

    Continuation of [IntroUF.v] - [IntroUF4.v] and [Bridge.v], with the
    same conventions: path composition [q ⋅ p :≡ p ∙ q], fibers and
    pointing paths with [y = f x], and notions that occur definitionally
    in Coq-HoTT defined from the library notion and used under the
    book's name.  Results that need univalence assume Coq-HoTT's
    [Univalence]. *)

(** ** Preliminaries *)

(** Identifications in a sum type with proposition-valued second
    component. *)
Definition path_sigma_prop {A : Type} {P : A -> Type}
  (hP : forall a, isProp (P a)) {u v : {a : A & P a}} (e : fst u = fst v)
  : u = v
  := pathpair (Y := P) (y := snd u) (y' := snd v) e (hP _ _ _).

(** A sum of contractible types over a contractible type is contractible. *)
Definition Sigma_isContr {A : Type} {B : A -> Type} (cA : isContr A)
  (cB : forall a, isContr (B a)) : isContr {a : A & B a}.
Proof.
  refine ((fst cA; fst (cB (fst cA))); _).
  intros [a b].
  exact (pathpair (snd cA a) (isContr_isProp' (cB a) _ _)).
Defined.

(** A map between contractible types is an equivalence. *)
Definition contr_map_isEquiv {A B : Type} (cA : isContr A) (cB : isContr B)
  (f : A -> B) : isEquiv f
  := iso_to_isEquiv f (fun _ => fst cA) (fun a => snd cA a)
       (fun b => isContr_isProp' cB _ _).

(** Equivalences of families of types induce equivalences of products. *)
Definition Pi_eqv `{Funext} {A : Type} {B C : A -> Type}
  (e : forall a, B a ≃ C a) : (forall a, B a) ≃ (forall a, C a)
  := mkEqv (fun k a => fst (e a) (k a)) (fun k a => eqinv (snd (e a)) (k a))
       (fun k => ptw_inv (fun a => eqinv_l (snd (e a)) (k a)))
       (fun k => ptw_inv (fun a => eqinv_r (snd (e a)) (k a))).

(** The type [∑_{b:B} (b = c)] is contractible. *)
Definition singleton_contr' {B : Type} (c : B) : isContr {b : B & b = c}.
Proof.
  refine ((c; refl); _).
  intros [b p]. revert b p. refine (paths_ind_r _ _ _). exact refl.
Defined.

(** ** 2.19 The replacement principle *)

Section Smallness.

  Universe u.

  (** Definition [def:ess-loc-small]. *)
  Definition essSmall (A : Type) : Type := {X : Type@{u} & A ≃ X}.

  Definition locSmall (A : Type) : Type := forall x y : A, essSmall (x = y).

  (** Essential smallness is invariant under equivalence. *)
  Definition essSmall_Eqv {A B : Type} (e : A ≃ B) (s : essSmall B)
    : essSmall A
    := (fst s; Eqv_comp e (snd s)).

  (** Any [A : U] is essentially small. *)
  Definition small_essSmall (A : Type@{u}) : essSmall A := (A; idEqv A).

  (** Any essentially small type is locally small. *)
  Definition essSmall_locSmall {A : Type} (s : essSmall A) : locSmall A.
  Proof.
    intros x y.
    pose (E := IsEquiv_of_isEquiv (snd (snd s))).
    exact ((fst (snd s) x = fst (snd s) y);
           (ap (fst (snd s)); isEquiv_of_IsEquiv _ (H := isequiv_ap x y))).
  Defined.

  (** A reflexive relation [Eq_A : A → A → U] that induces, by path
      induction, equivalences [(x = y) ≃ Eq_A(x,y)] shows that [A] is
      locally small. *)
  Definition locSmall_of_Eq {A : Type} (Eq : A -> A -> Type@{u})
    (r : forall x, Eq x x)
    (h : forall x y, isEquiv (path_ind x (fun y _ => Eq x y) (r x) y))
    : locSmall A
    := fun x y => (Eq x y; (_; h x y)).

  (** Exercise: [U] is locally [U]-small, by univalence. *)
  Definition U_locSmall `{UnivalenceUF} : locSmall Type@{u}
    := fun X Y => ((X ≃ Y); (idtoeqv; ua X Y)).

  (** Exercise: closure under products over a small type. *)
  Definition Pi_locSmall `{Funext} {A : Type@{u}} {B : A -> Type}
    (h : forall a, locSmall (B a)) : locSmall (forall a, B a).
  Proof.
    intros f g.
    exact ((forall a, fst (h a (f a) (g a)));
           Eqv_comp (ptw; funext f g) (Pi_eqv (fun a => snd (h a (f a) (g a))))).
  Defined.

  (** Being essentially small is a proposition, by univalence. *)
  Definition Eqv_precomp `{Funext} {A X X' : Type} (e : A ≃ X)
    : (X ≃ X') ≃ (A ≃ X').
  Proof.
    refine (mkEqv (fun d => Eqv_comp e d) (fun d => Eqv_comp (Eqv_inv e) d) _ _).
    - intro d. apply path_Eqv. apply ptw_inv. intro x.
      exact (ap (fst d) (eqinv_r (snd e) x)).
    - intro d. apply path_Eqv. apply ptw_inv. intro a.
      exact (ap (fst d) (eqinv_l (snd e) a)).
  Defined.

  Definition essSmall_isProp `{Univalence} (A : Type) : isProp (essSmall A).
  Proof.
    intros s s'. revert s'.
    apply isContr_isProp'.
    destruct s as [X e].
    refine (isContr_Eqv _ (singleton_contr X)).
    exact (tot (fun X' (p : X = X') => fst (Eqv_precomp e) (idtoeqv p));
           tot_isEquiv _ (fun X' => snd (Eqv_comp (idtoeqv; ua X X') (Eqv_precomp e)))).
  Defined.

End Smallness.

(** Remark: propositional resizing says that any proposition is
    essentially small, and then any set is locally small. *)
Section ResizingSmall.

  Universes u v.
  Constraint u < v.

  (** Propositional resizing from [U] to [U'] ([PropResizing] in
      [IntroUF4.v]), with the lifting map written out at levels [u], [v]. *)
  Definition lift_uv (P : {X : Type@{u} & isProp X}) : {X : Type@{v} & isProp X}
    := exist (fun X : Type@{v} => isProp X) (fst P) (fun a b => snd P a b).

  Definition resizing_essSmall (r : isEquiv lift_uv)
    (P : {X : Type@{v} & isProp X}) : {X : Type@{u} & fst P ≃ X}.
  Proof.
    pose (e := eqinv_r r P).
    exact (exist (fun X : Type@{u} => fst P ≃ X) (fst (eqinv r P))
             (Eqv_inv (idtoeqv (ap fst e)))).
  Defined.

  Definition resizing_set_locSmall (r : isEquiv lift_uv) (A : Type@{v})
    (s : isSet A) (x y : A) : {X : Type@{u} & (x = y) ≃ X}
    := resizing_essSmall r ((x = y); s x y).

End ResizingSmall.

(** Principle [pri:replacement]. *)
Definition Replacement : Type
  := forall (A B : Type) (f : A -> B), essSmall A -> locSmall B
       -> essSmall (im f).

(** Exercise [xca:comp-loc-small-ess-small]: under replacement, the
    connected component of an element of a locally small type is
    essentially small. *)
Definition component_im_eqv {A : Type} (a : A)
  : component A a ≃ im (fun _ : True => a)
  := (tot (fun x => ptrunc_rec ptrunc_isProp
                      (fun p : a = x => trunc ((triv; p⁻¹) : {_ : True & x = a}))) ;
      tot_isEquiv _ (fun x =>
        snd (Eqv_of_props ptrunc_isProp ptrunc_isProp
               (ptrunc_rec ptrunc_isProp
                  (fun p : a = x => trunc ((triv; p⁻¹) : {_ : True & x = a})))
               (ptrunc_rec ptrunc_isProp
                  (fun w : {_ : True & x = a} => trunc (snd w)⁻¹))))).

Definition replacement_component (rep : Replacement) {A : Type}
  (h : locSmall A) (a : A) : essSmall (component A a)
  := essSmall_Eqv (component_im_eqv a)
       (rep True A (fun _ => a) (small_essSmall True) h).

(** ** 2.20 Predicates and subtypes *)

(** Definition [def:predicate]: a predicate on [T] is a family of
    propositions, i.e. a map [T → Prop]. *)
Definition isDecPred {T : Type} (P : T -> PropU) : Type
  := forall t, isDecidable (fst (P t)).

(** The characteristic function of a decidable predicate. *)
Definition chi {T : Type} {P : T -> PropU} (d : isDecPred P) : T -> Bool
  := fun t => match d t with inl _ => yes | inr _ => no end.

Definition chi_spec {T : Type} {P : T -> PropU} (d : isDecPred P) (t : T)
  : ((chi d t = yes) -> fst (P t)) × (fst (P t) -> chi d t = yes).
Proof.
  unfold chi. destruct (d t) as [p|np].
  - exact ((fun _ => p); (fun _ => refl)).
  - exact ((fun e => match yes_ne_no e⁻¹ with end);
           (fun p => match np p with end)).
Defined.

(** Exercise [xca:decidability]. *)
Definition bool_pred {T : Type} (f : T -> Bool) : T -> PropU
  := fun t => ((f t = yes); isSet_bool _ _).

Definition bool_pred_isDec {T : Type} (f : T -> Bool) : isDecPred (bool_pred f).
Proof.
  intro t. unfold bool_pred; cbn. destruct (f t).
  - exact (inl refl).
  - exact (inr (fun e => yes_ne_no e⁻¹)).
Defined.

Definition dec_prop_True_False {P : Type} (hP : isProp P) (d : isDecidable P)
  : (P ≃ True) ⨿ (P ≃ False)
  := match d with
     | inl p => inl (Eqv_of_props hP True_isProp (fun _ => triv) (fun _ => p))
     | inr np => inr (Eqv_of_props hP False_isProp np
                       (fun x => match x with end))
     end.

(** Definition [def:subtype]: the type of subtypes [Sub(T) :≡ (T → Prop)]
    and the underlying type [T_P :≡ ∑_{t:T} P(t)]. *)
Definition Sub (T : Type) : Type := T -> PropU.

Definition carrier {T : Type} (P : T -> PropU) : Type := {t : T & fst (P t)}.

(** Lemma [lem:subtype-eq-=].  The first projection is an injection: we
    show directly that its fibers are propositions (the book uses
    [cor:contract-away]), and apply [lem:inj-ap]. *)
Definition fst_isInj {T : Type} {Q : T -> Type} (hQ : forall t, isProp (Q t))
  : isInj (@fst T Q).
Proof.
  intros t [[y u] e] [[y' u'] e'].
  change (t = y) in e. change (t = y') in e'.
  destruct e, e'.
  exact (ap (fun u0 => (((t; u0) : {t : T & Q t}); refl) : fiber fst t)
            (hQ t u u')).
Defined.

Definition subtype_paths_eqv {T : Type} {Q : T -> Type}
  (hQ : forall t, isProp (Q t)) (w w' : {t : T & Q t})
  : (w = w') ≃ (fst w = fst w')
  := (ap fst; isInj_ap_isEquiv (fst_isInj hQ) w w').

Definition subtype_eq {T : Type} (P : T -> PropU) (w w' : carrier P)
  : isEquiv (@ap (carrier P) T fst w w')
  := snd (subtype_paths_eqv (fun t => snd (P t)) w w').

(** Example [def:Prop-Set]: [Prop_U] and [Set_U] (here [PropU] and [SetU],
    from [IntroUF4.v]) are subtypes of [U]. *)
Definition PropU_paths_eqv `{Funext} (P Q : PropU) : (P = Q) ≃ (fst P = fst Q)
  := subtype_paths_eqv (fun X => isProp_isProp X) P Q.

(** Lemma [lem:Prop-in-Set]. *)
Definition PropU_isSet `{Univalence} : isSet PropU.
Proof.
  intros P Q.
  apply (isProp_Eqv (Eqv_inv (PropU_paths_eqv P Q))).
  apply (isProp_Eqv (Eqv_inv ((@idtoeqv (fst P) (fst Q)); ua (fst P) (fst Q)))).
  exact (Sigma_isProp (fun_isProp (snd Q)) (fun f => isEquiv_isProp f)).
Defined.

(** Hence [Sub(T)] is a set. *)
Definition Sub_isSet `{Univalence} (T : Type) : isSet (Sub T).
Proof.
  apply IsHSet_isSet. pose proof (isSet_IsHSet PropU_isSet).
  unfold Sub. exact _.
Defined.

(** Exercise [xca:subtype-univ-prop]: the universal property of
    subtypes. *)
Definition subtype_univ_prop `{Funext} {T X : Type} (f : X -> T)
  (P : T -> PropU)
  : ((forall x, fst (P (f x))) -> isContr {g : X -> carrier P & f = fst ∘ g})
    × (isContr {g : X -> carrier P & f = fst ∘ g} -> forall x, fst (P (f x)))
  := (fun h => isContr_Eqv (section_above_f (Y := fun t => fst (P t)) f)
                 (isProp_inhabited_isContr
                    (Pi_isProp (fun x => snd (P (f x)))) h);
      fun c => fst (Eqv_inv (section_above_f (Y := fun t => fst (P t)) f))
                 (fst c)).

(** Definition [def:injtype]: the type of injections into [T]. *)
Section SubInj.

  Universe u.
  Context (T : Type@{u}).

  Definition Inj : Type := {S : Type@{u} & {f : S -> T & isInj f}}.

  Definition isInj_isProp `{Funext} {S : Type} (f : S -> T) : isProp (isInj f)
    := Pi_isProp (fun t => isProp_isProp _).

  Definition Sub_to_Inj (P : T -> {X : Type@{u} & isProp X}) : Inj
    := (carrier P; (fst; fst_isInj (fun t => snd (P t)))).

  Definition Inj_to_Sub (w : Inj) : T -> {X : Type@{u} & isProp X}
    := fun t => (fiber (fst (snd w)) t; snd (snd w) t).

  (** Lemma [lem:Sub(T)=Inj(T)] and Exercise [xca:Sub(T)=Inj(T)]. *)

  Definition Inj_Sub_Inj_carrier (w : Inj)
    : carrier (Inj_to_Sub w) ≃ fst w.
  Proof.
    destruct w as [S [i j]].
    refine (mkEqv (fun v => fst (snd v)) (fun s => (i s; (s; refl))) _ _).
    - intros [t [s e]]. cbn in e |- *.
      revert t e. refine (paths_ind_r _ _ _). exact refl.
    - intro s. exact refl.
  Defined.

  Definition trp_fun_dom {X Y : Type} {Z : Type} (e : X = Y) (g : X -> Z)
    : trp (fun W : Type => W -> Z) e g = g ∘ trp (fun W : Type => W) e⁻¹.
  Proof. destruct e. exact refl. Defined.

  Definition trp_sigma_fst {X Y : Type} {Z : Type}
    (Q : forall W : Type, (W -> Z) -> Type) (e : X = Y)
    (w : {f : X -> Z & Q X f})
    : fst (trp (fun W : Type => {f : W -> Z & Q W f}) e w)
      = trp (fun W : Type => W -> Z) e (fst w).
  Proof. destruct e. exact refl. Defined.

  Definition trp_inv_eqinv {X Y : Type} (e : X = Y) (E : X ≃ Y)
    (h : ptoe e = fst E) (y : Y)
    : trp (fun W : Type => W) e⁻¹ y = eqinv (snd E) y
    := (eqinv_l (snd E) _)^ @ ap (eqinv (snd E)) ((ptw h _)^ @ trp_trp_inv e y).

  Definition Sub_Inj_isEquiv `{Univalence} : isEquiv Sub_to_Inj.
  Proof.
    refine (iso_to_isEquiv Sub_to_Inj Inj_to_Sub _ _).
    - intro P. apply ptw_inv. intro t.
      exact (path_PropU (P := Inj_to_Sub (Sub_to_Inj P) t) (Q := P t)
               (fun w : fiber (@fst T (fun t => fst (P t))) t =>
                  trp (fun t => fst (P t)) (snd w)⁻¹ (snd (fst w)))
               (fun p => (((t; p) : carrier P); refl))).
    - intros [S [i j]].
      pose (E := Inj_Sub_Inj_carrier (S; (i; j))).
      refine (pathpair (etop E) _).
      apply (path_sigma_prop isInj_isProp).
      refine (trp_sigma_fst (fun W f => isInj f) (etop E) _ @ _).
      refine (trp_fun_dom (etop E) fst @ _).
      apply ptw_inv. intro s. cbn.
      refine (ap fst (trp_inv_eqinv (etop E) E (ap fst (ptoe_etop E)) s) @ _).
      pose (v := eqinv (snd E) s).
      exact (snd (snd v) @ ap i (eqinv_r (snd E) s)).
  Defined.

  Definition Sub_Inj_eqv `{Univalence}
    : (T -> {X : Type@{u} & isProp X}) ≃ Inj
    := (Sub_to_Inj; Sub_Inj_isEquiv).

End SubInj.

(** Corollary [cor:subtype-same-level]: for [n ≥ -1], subtypes of
    [n]-types are [n]-types. *)
Definition subtype_paths_Q (Q : Type -> Type)
  (Qinv : forall X Y : Type, X ≃ Y -> Q X -> Q Y)
  {T : Type} {R : T -> Type} (hR : forall t, isProp (R t))
  (h : forall x y : T, Q (x = y))
  : forall w w' : {t : T & R t}, Q (w = w')
  := fun w w' => Qinv _ _ (Eqv_inv (subtype_paths_eqv hR w w')) (h _ _).

Definition subtype_isProp {T : Type} {R : T -> Type}
  (hR : forall t, isProp (R t)) (hT : isProp T) : isProp {t : T & R t}
  := Sigma_isProp hT hR.

Definition subtype_ntype (n : ℕ) {T : Type} {R : T -> Type}
  (hR : forall t, isProp (R t)) (hT : is_ntype n T)
  : is_ntype n {t : T & R t}.
Proof.
  destruct n as [|n].
  - exact (subtype_paths_Q isProp isProp_Qinv hR hT).
  - exact (subtype_paths_Q (is_ntype n) (is_ntype_Qinv n) hR hT).
Defined.

(** Exercise [xca:subsets-inclusion]: inclusion of subtypes is a partial
    order with a least and a greatest element. *)
Definition subset_incl {T : Type} (P0 P1 : Sub T) : Type
  := forall t, fst (P0 t) -> fst (P1 t).

Notation "P ⊆ Q" := (subset_incl P Q) : uf_scope.

Section SubsetInclusion.

  Context {T : Type}.

  Definition subset_incl_isProp `{Funext} (P0 P1 : Sub T) : isProp (P0 ⊆ P1)
    := Pi_isProp (fun t => fun_isProp (snd (P1 t))).

  Definition subset_incl_refl (P : Sub T) : P ⊆ P := fun t p => p.

  Definition subset_incl_trans (P0 P1 P2 : Sub T)
    : P0 ⊆ P1 -> P1 ⊆ P2 -> P0 ⊆ P2
    := fun a b t p => b t (a t p).

  Definition subset_incl_antisym `{Univalence} (P0 P1 : Sub T)
    : P0 ⊆ P1 -> P1 ⊆ P0 -> P0 = P1
    := fun a b => ptw_inv (fun t => path_PropU (a t) (b t)).

  Definition empty_sub : Sub T := fun _ => (False; False_isProp).
  Definition full_sub : Sub T := fun _ => (True; True_isProp).

  Definition empty_sub_least (P : Sub T) : empty_sub ⊆ P
    := fun t x => match x with end.

  Definition full_sub_greatest (P : Sub T) : P ⊆ full_sub
    := fun t _ => triv.

End SubsetInclusion.

(** Definition [def:decidable-set]. *)
Definition isDecSet (A : Type) : Type
  := forall x y : A, isProp (x = y) × isDecidable (x = y).

(** Theorem [thm:hedberg]: the library's [hset_decpaths]. *)
Definition hedberg {A : Type} (d : forall x y : A, (x = y) ⨿ ¬ (x = y))
  : isDecSet A
  := fun x y => (IsHSet_isSet (@hset_decpaths A d) x y; d x y).

(** ** 2.21 Pointed types

    The book's pointed types are pairs, and its pointing paths have the
    form [pt_Y = f(pt_X)]; the library's [pType] is a record and its
    pointed maps have pointing paths [f(pt) = pt], so we use our own
    definitions. *)

(** Definition [def:pointedtypes]. *)
Definition Ustar : Type := {A : Type & A}.

(** The underlying type [X_÷] and the base point [pt_X]. *)
Definition utype (X : Ustar) : Type := fst X.
Definition pt (X : Ustar) : utype X := snd X.

(** [A_+ :≡ (A ⨿ True, inr triv)]. *)
Definition plus (A : Type) : Ustar := ((A ⨿ True); inr triv).

(** Pointed functions [X →* Y], the fiber of [ev_{pt_X}] at [pt_Y]. *)
Definition pmap (X Y : Ustar) : Type
  := fiber (@ev (utype X) (fun _ => utype Y) (pt X)) (pt Y).

Notation "X →* Y" := (pmap X Y) (at level 99) : uf_scope.

Definition pmap_unfold (X Y : Ustar)
  : (X →* Y) = {f : utype X -> utype Y & pt Y = f (pt X)} := refl.

(** Composition [gf :≡ (g_÷ f_÷, g_÷(f_pt) · g_pt)]. *)
Definition pcomp {X Y Z : Ustar} (g : Y →* Z) (f : X →* Y) : X →* Z
  := (fst g ∘ fst f; ap (fst g) (snd f) ⋅ snd g).

(** Definition [def:pointedidentity]. *)
Definition pid (X : Ustar) : X →* X := (id (utype X); refl).

(** Exercise [xca:plusforgetadjoint]. *)
Definition plus_adjoint `{Funext} (A : Type) (B : Ustar)
  : (A -> utype B) ≃ (plus A →* B).
Proof.
  refine (mkEqv
            (fun h => ((fun z => match z with
                                 | inl a => h a
                                 | inr _ => pt B
                                 end); refl))
            (fun k => fst k ∘ inl) (fun h => refl) _).
  intros [k p].
  pose (Hk := fun z : A ⨿ True =>
               match z return match z with
                              | inl a => k (inl a)
                              | inr _ => pt B
                              end = k z with
               | inl a => refl
               | inr t => match t with triv => p end
               end).
  refine (pathpair (ptw_inv Hk) _).
  refine (trptw (x := inr triv) (y := pt B) (ptw_inv Hk) refl @ trans_1p _ @ _).
  exact (ap (fun F => F (inr triv)) (eqinv_r (funext _ _) Hk)).
Defined.

(** Exercise [xca:freemaps]. *)
Definition freemaps (A : Ustar) (B : Type)
  : {b : B & A →* (B; b)} ≃ (utype A -> B).
Proof.
  refine (mkEqv (fun w => fst (snd w))
                (fun f => (f (pt A); ((f; refl) : A →* (B; f (pt A))))
                          : {b : B & A →* (B; b)})
                _ (fun f => refl)).
  intros [b [f p]]. change (utype A -> B) in f. cbn in p |- *.
  revert b p. refine (paths_ind_r _ _ _). exact refl.
Defined.

(** Definition [def:pointedequiv]. *)
Definition pEqv (X Y : Ustar) : Type := {f : X →* Y & isEquiv (fst f)}.

Notation "X ≃* Y" := (pEqv X Y) (at level 85) : uf_scope.

(** Exercise [xca:pointedequiv]. *)
Definition pdiv {X Y : Ustar} (p : X = Y) : utype X = utype Y := ap utype p.

Definition ppt {X Y : Ustar} (p : X = Y) : pt Y = ptoe (pdiv p) (pt X)
  := match p with refl => refl end.

Definition path_to_pEqv {X Y : Ustar} (p : X = Y) : X ≃* Y
  := ((ptoe (pdiv p); ppt p); trp_isEquiv (fun T : Type => T) (pdiv p)).

Definition pEqv_total_isContr `{Univalence} (X : Ustar)
  : isContr {Y : Ustar & X ≃* Y}.
Proof.
  destruct X as [A a].
  pose (fw := fun v : {Y : Ustar & (A; a) ≃* Y} =>
       ((fst (fst v); (fst (fst (snd v)); snd (snd v))) : {B : Type & A ≃ B};
        (snd (fst v); snd (fst (snd v))))
       : {w : {B : Type & A ≃ B} & {b : fst w & b = fst (snd w) a}}).
  pose (bw := fun u : {w : {B : Type & A ≃ B} & {b : fst w & b = fst (snd w) a}} =>
       (((fst (fst u); fst (snd u)) : Ustar;
        ((fst (snd (fst u)); snd (snd u)); snd (snd (fst u))))
        : {Y : Ustar & (A; a) ≃* Y})).
  assert (Re : {Y : Ustar & (A; a) ≃* Y}
               ≃ {w : {B : Type & A ≃ B} & {b : fst w & b = fst (snd w) a}}).
  { refine (mkEqv fw bw _ _).
    - intros [[B b] [[f p] e]]. exact refl.
    - intros [[B [f e]] [b p]]. exact refl. }
  refine (isContr_Eqv (Eqv_inv Re) _).
  refine (Sigma_isContr _ (fun w => singleton_contr' _)).
  exact (isContr_Eqv (tot (fun B (p : A = B) => idtoeqv p);
                      tot_isEquiv _ (fun B => ua A B))
                     (singleton_contr A)).
Defined.

Definition path_to_pEqv_isEquiv `{Univalence} (X Y : Ustar)
  : isEquiv (@path_to_pEqv X Y)
  := isEquiv_from_tot (fun Y => @path_to_pEqv X Y)
       (contr_map_isEquiv (singleton_contr X) (pEqv_total_isContr X) _) Y.

(** Construction [con:identity-ptd-maps]: [ptw_*], following the book's
    chain of equivalences. *)
Definition ptw_star `{Funext} {X Y : Ustar} (f g : X →* Y)
  : (f = g) ≃ {h : forall x, fst f x = fst g x & h (pt X) ⋅ snd f = snd g}.
Proof.
  destruct f as [f fp], g as [g gp].
  refine (Eqv_comp (Eqv_inv (path_sigma_eqv (Y := fun k => pt Y = k (pt X)))) _).
  refine (Eqv_comp (sum_equiv_base (funext f g)
                      (fun e => PathOver (fun k => pt Y = k (pt X)) e fp gp)) _).
  pose (E := fun h : forall x, f x = g x =>
               Eqv_comp (eq_l_eqv (w := gp) (trptw (ptw_inv h) fp))
                        (eq_l_eqv (w := gp) (ap (fun H : (forall x, f x = g x) => H (pt X) ⋅ fp)
                                      (eqinv_r (funext f g) h)))).
  exact (tot (fun h => fst (E h)); tot_isEquiv _ (fun h => snd (E h))).
Defined.

(** Exercise [xca:identity-ptd-maps]: [ptw_*] by induction. *)
Definition ptw_star_ind {X Y : Ustar} {f g : X →* Y} (e : f = g)
  : {h : forall x, fst f x = fst g x & h (pt X) ⋅ snd f = snd g}
  := match e with refl => ((fun x => refl); refl) end.

(** Exercise [xca:filler-ptd-sum-of-fibers]. *)
Section SumOfFibers.

  Context {X Y : Ustar} (f : X →* Y).

  Definition SumFib : Ustar
    := ({y : utype Y & fiber (fst f) y}; (pt Y; (pt X; snd f))).

  Definition sumfib_e : SumFib →* X := ((fun w => fst (snd w)); refl).

  Definition sumfib_e_isEquiv : isEquiv (fst sumfib_e).
  Proof.
    refine (iso_to_isEquiv _ (fun x => (fst f x; (x; refl))) _ (fun x => refl)).
    intros [y [x p]]. cbn in p |- *.
    revert y p. refine (paths_ind_r _ _ _). exact refl.
  Defined.

  Definition sumfib_fst : SumFib →* Y := (fst; refl).

  Definition sumfib_filler `{Funext} : sumfib_fst = pcomp f sumfib_e
    := eqinv (snd (ptw_star sumfib_fst (pcomp f sumfib_e)))
         ((fun w : utype SumFib => snd (snd w)); trans_1p (snd f)).

End SumOfFibers.

(** Exercise [xca:ptd-equiv-inv]: the pointed inverse of a pointed
    equivalence.  We take the (unpointed) inverse together with the
    half-adjoint data provided by Coq-HoTT ([eissect], [eisretr],
    [eisadj]) for [isequiv_adjointify]; its inverse function is the
    book's [f⁻¹]. *)
Section PointedInverse.

  Context {X Y : Ustar} (f : X ≃* Y).

  Let F := fst (fst f).
  Let fp : pt Y = F (pt X) := snd (fst f).
  Let E : IsEquiv F := IsEquiv_of_isEquiv (snd f).
  Let g := @equiv_inv _ _ F E.
  Let η := @eissect _ _ F E.
  Let ε := @eisretr _ _ F E.

  Definition pinv : Y ≃* X
    := ((g; (η (pt X) ⋅ ap g fp)⁻¹); eqinv_isEquiv (snd f)).

  Definition pinv_aux1 {Z : Type} {u v w : Z} (a : u = v) (b : v = w)
    : b ⋅ (a ⋅ (b ⋅ a)⁻¹) = refl.
  Proof. destruct b, a. exact refl. Defined.

  Definition pinv_left `{Funext}
    : pcomp (fst pinv) (fst f) = pid X
    := eqinv (snd (ptw_star (pcomp (fst pinv) (fst f)) (pid X)))
         (η; pinv_aux1 (ap g fp) (η (pt X))).

  Definition pinv_aux2 {u v : utype X} (p : u = v)
    : ap F p ⋅ (ap F ((p ⋅ refl)⁻¹) ⋅ refl) = refl.
  Proof. destruct p. exact refl. Defined.

  Definition pinv_aux3 (x0 : utype X)
    : forall (y : utype Y) (q : y = F x0),
      ε y ⋅ (ap F ((η x0 ⋅ ap g q)⁻¹) ⋅ q) = refl.
  Proof.
    refine (paths_ind_r _ _ _).
    refine (ap (fun e => e ⋅ (ap F ((η x0 ⋅ refl)⁻¹) ⋅ refl))
               (@eisadj _ _ F E x0) @ _).
    exact (pinv_aux2 (η x0)).
  Defined.

  Definition pinv_right `{Funext}
    : pcomp (fst f) (fst pinv) = pid Y
    := eqinv (snd (ptw_star (pcomp (fst f) (fst pinv)) (pid Y)))
         (ε; pinv_aux3 (pt X) (pt Y) fp).

End PointedInverse.

(** * Part 6: Section 2.22

    ** Summary of this formalization

    Section 2.22 is formalized in this file, which builds on [IntroUF.v] -
    [IntroUF5.v] and [Bridge.v].  It compiles, with nothing admitted.
    [Print Assumptions]: [Funext] and [Univalence] are used only where
    needed, and Coq-HoTT's [istrunc_truncation] (and [gqglue] for the
    library's quotients) for results involving truncations.

    Book notions defined from Coq-HoTT notions: the set truncation
    [‖T‖₀ :≡ strunc T :≡ Trunc 0 T] with [|t|₀ :≡ tr t] (its induction
    principle computes by definition), and the quotient as a higher
    inductive type, [def:quotient-as-HIT], which is the library's
    [Quotient] ([QuotHIT]).  The book's main quotient [A/R], the image of
    [R : A → (A → Prop)], is our own ([quot], with classes [cls]).
    For a function of two non-dependent arguments the book's [apap] is the
    library's [ap011].

    What's covered
    - [lem:Set-is-groupoid]: equivalences and identifications between
      propositions (sets) form propositions (sets); [Set] is a groupoid.
    - [thm:isset-inductive-types] for lists, following Simon Huber's
      method as in the book, and exercise [xca:set-sum] (binary sums).
    - Set truncation: induction and recursion principles and the
      universal property; exercise [xca:sum-of-conn-components] (the
      components [A_(z)] for [z : ‖A‖₀] with [A_(|a|₀) ≡ A_(a)],
      [A ≃ ∑_z A_(z)], and [A] connected iff [‖A‖₀] contractible, using the
      library's [equiv_path_Tr] for [(|x|₀ = |y|₀) ≃ ‖x = y‖]); exercise
      [xca:subset-of-set-trunc].
    - Weakly constant maps and [thm:wconstant-elim], via the image.
    - Set quotients: [lem:equiv-class-prop], [thm:quotient-property]
      (both parts, with [f̄([x]) ≡ f(x)]), exercise [xca:A/True-prop-trunc],
      exercise [xca:quotients-equivalence] ([A/R ≃ QuotHIT]), remark
      [rem:set-trunc-as-quotient], and exercise [xca:map-induces-quotient]
      (the unique equivalence [e_f : A/≡_f ≃ ‖im(f)‖₀]).

    Left out
    - Exercise [xca:ints-as-quotient] (integers as a quotient of [ℕ × ℕ])
      is formalized in [IntroUF7.v], since it uses the results on [ℕ] of
      2.23.
    - The other inductive types of 2.12 in [thm:isset-inductive-types]
      (left to the reader in the book); [ℕ] is shown to be a set in
      [IntroUF7.v] via Hedberg's theorem.

    ** Conventions

    Continuation of [IntroUF.v] - [IntroUF5.v] and [Bridge.v], with the
    same conventions: path composition [q ⋅ p :≡ p ∙ q], fibers with
    [y = f x], and notions that occur definitionally in Coq-HoTT defined
    from the library notion and used under the book's name.  Results that
    need univalence assume Coq-HoTT's [Univalence]. *)

(** ** Preliminaries *)

Definition Pi_isSet `{Funext} {A : Type} {B : A -> Type}
  (h : forall a, isSet (B a)) : isSet (forall a, B a).
Proof.
  apply IsHSet_isSet. pose proof (fun a => isSet_IsHSet (h a)). exact _.
Defined.

Definition Sigma_isSet {A : Type} {B : A -> Type} (sA : isSet A)
  (sB : forall a, isSet (B a)) : isSet {a : A & B a}.
Proof.
  apply IsHSet_isSet. pose proof (isSet_IsHSet sA).
  pose proof (fun a => isSet_IsHSet (sB a)). exact _.
Defined.

(** Every type is equivalent to the sum of the fibers of a map into it. *)
Definition total_fibers {X Y : Type} (f : X -> Y) : X ≃ {y : Y & fiber f y}.
Proof.
  refine (mkEqv (fun x => (f x; (x; refl)))
                (fun w => fst (snd w)) (fun x => refl) _).
  intros [y [x p]]. cbn in p |- *.
  revert y p. refine (paths_ind_r _ _ _). exact refl.
Defined.

(** Induction on the image, for families of propositions. *)
Definition im_ind {A B : Type} (f : A -> B) (Q : im f -> Type)
  (hQ : forall z, isProp (Q z)) (g : forall a, Q (im_p f a)) : forall z, Q z.
Proof.
  intros [y u]. revert u.
  refine (ptrunc_ind (fun u => Q (y; u)) (fun _ => hQ _) _).
  intros [a e]. revert y e. refine (paths_ind_r _ _ _). exact (g a).
Defined.

(** ** 2.22 Operations that produce sets *)

(** Lemma [lem:Set-is-groupoid]. *)
Definition Eqv_props_isProp `{Funext} {X Y : Type} (hY : isProp Y)
  : isProp (X ≃ Y)
  := Sigma_isProp (fun_isProp hY) (fun f => isEquiv_isProp f).

Definition paths_props_isProp `{Univalence} {X Y : Type} (hY : isProp Y)
  : isProp (X = Y)
  := isProp_Eqv (Eqv_inv (idtoeqv; ua X Y)) (Eqv_props_isProp hY).

Definition Eqv_sets_isSet `{Funext} {X Y : Type} (sY : isSet Y)
  : isSet (X ≃ Y)
  := subtype_ntype 0 (fun f => isEquiv_isProp f) (Pi_isSet (fun _ => sY)).

Definition paths_sets_isSet `{Univalence} {X Y : Type} (sY : isSet Y)
  : isSet (X = Y)
  := is_ntype_Eqv 0 (Eqv_inv (idtoeqv; ua X Y)) (Eqv_sets_isSet sY).

(** [Prop] is a set ([PropU_isSet] in [IntroUF5.v]) and [Set] is a
    groupoid. *)
Definition SetU_isGrpd `{Univalence} : isGrpd SetU
  := fun S T => is_ntype_Eqv 0
       (Eqv_inv (subtype_paths_eqv (fun X => isSet_isProp X) S T))
       (paths_sets_isSet (snd T)).

(** Theorem [thm:isset-inductive-types], for lists, following Simon
    Huber's method as in the book.  For a function of two non-dependent
    arguments the book's [apap] is the library's [ap011]. *)
Section ListsAreSets.

  Context {X : Type}.

  Definition T_list (l l' : X^*) : l = l' -> Type
    := match l as l0, l' as l0' return l0 = l0' -> Type with
       | nil, nil => fun p => p = refl
       | cons x l, cons x' l' =>
           fun p => {q : x = x' & {r : l = l' & p = ap011 cons q r}}
       | _, _ => fun _ => False
       end.

  Definition T_list_all (l l' : X^*) (p : l = l') : T_list l l' p.
  Proof.
    destruct p, l.
    - exact refl.
    - exact (refl; (refl; refl)).
  Defined.

  Definition list_loops (sX : isSet X) : forall (l : X^*) (p : l = l), p = refl.
  Proof.
    intro l. induction l as [|x l IH]; intro p.
    - exact (T_list_all _ _ p).
    - destruct (T_list_all _ _ p) as [q [r s]].
      exact (s @ ap011 (ap011 cons) (sX x x q refl) (IH r)).
  Defined.

  Definition list_isSet (sX : isSet X) : isSet (X^*).
  Proof. intros l l' p q. destruct q. exact (list_loops sX l p). Defined.

End ListsAreSets.

(** Exercise [xca:set-sum]. *)
Definition sum_isSet {X Y : Type} (sX : isSet X) (sY : isSet Y)
  : isSet (X ⨿ Y).
Proof.
  intros [x|y] [x'|y'].
  - exact (isProp_Eqv (Eqv_inv (path_inl_eqv x x')) (sX x x')).
  - intros p. destruct (inl_ne_inr x y' p).
  - intros p. destruct (encode_inr (X := X) p).
  - exact (isProp_Eqv (Eqv_inv (path_inr_eqv y y')) (sY y y')).
Defined.

(** Definition [def:set-truncation]: the set truncation [‖T‖₀] is the
    library's [Trunc 0 T], with element constructor [|t|₀ :≡ tr t].  Its
    induction principle satisfies [f(|t|₀) ≡ g(t)] by definition. *)
Definition strunc (T : Type) : Type := Trunc 0 T.

Definition settrunc {T : Type} : T -> strunc T := tr.

Definition strunc_isSet {T : Type} : isSet (strunc T)
  := @IsHSet_isSet _ (istrunc_truncation 0 T).

Definition strunc_ind {T : Type} (S : strunc T -> Type)
  (hS : forall x, isSet (S x)) (g : forall t, S (settrunc t))
  : forall x, S x
  := Trunc_ind S (Pt := fun x => isSet_IsHSet (hS x)) g.

Definition strunc_ind_trunc {T : Type} (S : strunc T -> Type) hS g (t : T)
  : strunc_ind S hS g (settrunc t) = g t := refl.

Definition strunc_rec {T S : Type} (hS : isSet S) (g : T -> S)
  : strunc T -> S
  := strunc_ind (fun _ => S) (fun _ => hS) g.

(** Induction into a family of propositions. *)
Definition strunc_ind_prop {T : Type} (S : strunc T -> Type)
  (hS : forall x, isProp (S x)) (g : forall t, S (settrunc t))
  : forall x, S x
  := strunc_ind S (fun x => prop_is_set (hS x)) g.

(** The universal property of set truncation. *)
Definition strunc_univ_prop `{Funext} (T : Type) {S : Type} (hS : isSet S)
  : (strunc T -> S) ≃ (T -> S)
  := mkEqv (fun h => h ∘ settrunc) (strunc_rec hS)
       (fun h => ptw_inv (strunc_ind_prop
                            (fun x => strunc_rec hS (h ∘ settrunc) x = h x)
                            (fun x => hS _ _) (fun t => refl)))
       (fun g => refl).

(** Exercise [xca:sum-of-conn-components]. *)
Section SumOfComponents.

  Context `{Univalence} {A : Type}.

  Definition strunc_component_pred : strunc A -> A -> PropU
    := strunc_rec (Pi_isSet (fun _ => PropU_isSet))
         (fun a x => ptrunc_PropU (a = x)).

  (** The connected component [A_(z)] for [z : ‖A‖₀]. *)
  Definition component_z (z : strunc A) : Type
    := {x : A & fst (strunc_component_pred z x)}.

  Definition component_z_trunc (a : A)
    : component_z (settrunc a) = component A a := refl.

  Definition component_z_iff (z : strunc A) (x : A)
    : ((z = settrunc x) -> fst (strunc_component_pred z x))
      × (fst (strunc_component_pred z x) -> z = settrunc x).
  Proof.
    revert z.
    refine (strunc_ind_prop _ (fun z => prod_isProp
              (fun_isProp (snd (strunc_component_pred z x)))
              (fun_isProp (strunc_isSet _ _))) _).
    intro a. cbn.
    exact ((fun e => equiv_inverse (equiv_path_Tr (n := -1) a x) e);
           ptrunc_rec (strunc_isSet _ _) (ap settrunc)).
  Defined.

  Definition sum_of_components : A ≃ {z : strunc A & component_z z}.
  Proof.
    refine (Eqv_comp (total_fibers settrunc) _).
    pose (F := fun z x => Eqv_of_props (strunc_isSet z (settrunc x))
                            (snd (strunc_component_pred z x))
                            (fst (component_z_iff z x)) (snd (component_z_iff z x))).
    pose (Fz := fun z => (tot (fun x => fst (F z x)) ;
                          tot_isEquiv _ (fun x => snd (F z x)))
                         : fiber settrunc z ≃ component_z z).
    exact (tot (fun z => fst (Fz z)); tot_isEquiv _ (fun z => snd (Fz z))).
  Defined.

  Definition isConn_strunc_isContr (c : isConn A) : isContr (strunc A).
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (fst c)). intro a.
    refine (settrunc a; _).
    refine (strunc_ind_prop _ (fun z => strunc_isSet _ _) _). intro x.
    exact (ptrunc_rec (strunc_isSet _ _) (ap settrunc) (snd c a x)).
  Defined.

  Definition strunc_isContr_isConn (c : isContr (strunc A)) : isConn A.
  Proof.
    refine (strunc_ind_prop (fun _ => ptrunc A) (fun _ => ptrunc_isProp)
              trunc (fst c); _).
    intros x y.
    exact (equiv_inverse (equiv_path_Tr (n := -1) x y)
             (isContr_isProp' c (settrunc x) (settrunc y))).
  Defined.

End SumOfComponents.

(** Exercise [xca:subset-of-set-trunc]. *)
Definition subset_of_strunc `{Funext} {A : Type} (P : strunc A -> PropU)
  : strunc {a : A & fst (P (settrunc a))} ≃ {b : strunc A & fst (P b)}.
Proof.
  pose (sS := Sigma_isSet strunc_isSet (fun b => prop_is_set (snd (P b)))).
  pose (e := strunc_rec sS (fun w : {a : A & fst (P (settrunc a))} =>
                              (settrunc (fst w); snd w) : {b : strunc A & fst (P b)})).
  pose (inv := fun w : {b : strunc A & fst (P b)} =>
                 strunc_ind (fun b => fst (P b) -> strunc {a : A & fst (P (settrunc a))})
                   (fun b => Pi_isSet (fun _ => strunc_isSet))
                   (fun a p => settrunc ((a; p) : {a : A & fst (P (settrunc a))}))
                   (fst w) (snd w)).
  refine (mkEqv e inv _ _).
  - refine (strunc_ind_prop _ (fun w => strunc_isSet _ _) _). intro w. exact refl.
  - intros [b p]. revert b p.
    refine (strunc_ind_prop (fun b => forall p, e (inv (b; p)) = (b; p))
              (fun b => Pi_isProp (fun p => sS _ _)) _).
    intros a p. exact refl.
Defined.

(** *** Weakly constant maps *)

Definition wconst {A B : Type} (f : A -> B) : Type
  := forall x x' : A, f x = f x'.

Definition wconst_isProp `{Funext} {A B : Type} (sB : isSet B) (f : A -> B)
  : isProp (wconst f)
  := Pi_isProp (fun x => Pi_isProp (fun x' => sB _ _)).

(** The image of a weakly constant map into a set is a proposition. *)
Definition im_isProp_wconst {A B : Type} {f : A -> B} (sB : isSet B)
  (c : wconst f) : isProp (im f).
Proof.
  intros [y1 z1] [y2 z2].
  pose (sI := im_isSet f sB).
  revert z1. refine (ptrunc_ind _ (fun _ => sI _ _) _). intros [x1 e1].
  revert z2. refine (ptrunc_ind _ (fun _ => sI _ _) _). intros [x2 e2].
  exact (path_sigma_prop (u := (y1; trunc (x1; e1)) : im f)
           (v := (y2; trunc (x2; e2)) : im f)
           (fun _ => ptrunc_isProp) (e2⁻¹ ⋅ (c x1 x2 ⋅ e1))).
Defined.

(** Theorem [thm:wconstant-elim]. *)
Definition wconst_elim {A B : Type} {f : A -> B} (sB : isSet B)
  (c : wconst f) : ptrunc A -> B
  := im_i f ∘ ptrunc_rec (im_isProp_wconst sB c) (im_p f).

Definition wconst_elim_trunc {A B : Type} {f : A -> B} (sB : isSet B)
  (c : wconst f) (x : A) : wconst_elim sB c (trunc x) = f x := refl.

(** *** Set quotients *)

Section Quotients.

  Context `{Univalence} {A : Type} (R : A -> A -> PropU)
    (rr : forall x, fst (R x x))
    (rs : forall x y, fst (R x y) -> fst (R y x))
    (rt : forall x y z, fst (R x y) -> fst (R y z) -> fst (R x z)).

  (** Definition [def:quotient-set]: [A/R] is the image of
      [R : A → (A → Prop)], with equivalence predicates [[a]]. *)
  Definition quot : Type := im R.

  Definition quot_isSet : isSet quot
    := im_isSet R (Pi_isSet (fun _ => PropU_isSet)).

  Definition cls (a : A) : quot := im_p R a.

  Definition cls_def (a : A) : cls a = (R a; trunc (a; refl)) := refl.

  (** Lemma [lem:equiv-class-prop]. *)
  Definition equiv_class_prop (P : quot) (a : A)
    : ((P = cls a) -> fst (fst P a)) × (fst (fst P a) -> P = cls a).
  Proof.
    refine ((fun e : P = cls a => trp (fun Q : quot => fst (fst Q a)) e⁻¹ (rr a)); _).
    intro h.
    pose (C := fun Q : quot => fst (fst Q a) -> forall x,
                 (fst (fst Q x) -> fst (R a x)) × (fst (R a x) -> fst (fst Q x))).
    assert (c' : forall Q, C Q).
    { refine (im_ind R C _ _).
      - intro Q. apply Pi_isProp. intro. apply Pi_isProp. intro x.
        exact (prod_isProp (fun_isProp (snd (R a x))) (fun_isProp (snd (fst Q x)))).
      - intros b hb x.
        exact ((fun rbx => rt a b x (rs b a hb) rbx);
               (fun rax => rt b a x hb rax)). }
    pose (c := c' P h).
    apply (path_sigma_prop (fun _ => ptrunc_isProp)).
    apply ptw_inv. intro x.
    exact (path_PropU (fst (c x)) (snd (c x))).
  Defined.

  (** Theorem [thm:quotient-property], first part. *)
  Definition cls_eq_iff (x x' : A)
    : ((cls x = cls x') -> fst (R x x')) × (fst (R x x') -> cls x = cls x')
    := equiv_class_prop (cls x) x'.

  (** Theorem [thm:quotient-property], second part (the universal
      property), with center [f̄] satisfying [f̄([x]) ≡ f(x)]. *)
  Section UniversalProperty.

    Context {B : Type} (sB : isSet B) (f : A -> B)
      (fr : forall x x', fst (R x x') -> f x = f x').

    Definition quot_wconst (z : quot)
      : wconst (fun w : {x : A & fst z = R x} => f (fst w)).
    Proof.
      intros [x e] [x' e']. apply fr.
      exact (trp (fun S : A -> PropU => fst (S x')) (e' ⋅ e⁻¹)⁻¹ (rr x')).
    Defined.

    Definition fbar : quot -> B
      := fun z => wconst_elim sB (quot_wconst z) (snd z).

    Definition fbar_cls (x : A) : fbar (cls x) = f x := refl.

    Definition quot_univ_prop : isContr {g : quot -> B & f = g ∘ cls}.
    Proof.
      refine ((fbar; refl); _).
      intros [g e].
      refine (pathpair (ptw_inv (im_ind R (fun z => fbar z = g z)
                                    (fun z => sB _ _) (fun x => ptw e x))) _).
      exact (Pi_isSet (fun _ => sB) _ _ _ _).
    Defined.

  End UniversalProperty.

  (** Definition [def:quotient-as-HIT]: the quotient as a higher inductive
      type is the library's [Quotient], whose induction principle into
      families of sets has the book's form (with paths over [qglue]) and
      computes by definition on [class_of]. *)
  Definition QuotHIT : Type := Quotient (A := A) (fun x y => fst (R x y)).

  (** Exercise [xca:quotients-equivalence]. *)
  Definition quot_QuotHIT : quot ≃ QuotHIT.
  Proof.
    pose (sQ := @IsHSet_isSet QuotHIT (ishset_quotient _)).
    pose (to := fbar sQ (class_of _) (fun x y r => qglue r)).
    pose (from := @Quotient_rec A (fun x y => fst (R x y)) quot
                    (isSet_IsHSet quot_isSet) cls
                    (fun x y r => snd (cls_eq_iff x y) r)).
    refine (mkEqv to from _ _).
    - refine (im_ind R _ (fun z => quot_isSet _ _) _). intro a. exact refl.
    - refine (Quotient_ind_hprop _ (fun w => to (from w) = w) _). intro a.
      exact refl.
  Defined.

End Quotients.

(** Exercise [xca:A/True-prop-trunc]. *)
Section QuotientByTrue.

  Context `{Univalence} (A : Type).

  Let R : A -> A -> PropU := fun _ _ => (True; True_isProp).

  Definition quot_True_isProp : isProp (quot R).
  Proof.
    intros z. revert z.
    refine (im_ind R _ (fun z => Pi_isProp (fun z' => quot_isSet R _ _)) _).
    intro x.
    refine (im_ind R _ (fun z' => quot_isSet R _ _) _). intro x'.
    exact (snd (cls_eq_iff R (fun _ => triv) (fun _ _ _ => triv)
                  (fun _ _ _ _ _ => triv) x x') triv).
  Defined.

  Definition quot_True_ptrunc : quot R ≃ ptrunc A
    := Eqv_of_props quot_True_isProp ptrunc_isProp
         (fbar R (fun _ => triv) (prop_is_set ptrunc_isProp) trunc
               (fun _ _ _ => ptrunc_isProp _ _))
         (ptrunc_rec quot_True_isProp (cls R)).

End QuotientByTrue.

(** Remark [rem:set-trunc-as-quotient]: the set truncation as the quotient
    by [R(x,y) :≡ ‖x = y‖]. *)
Section SetTruncAsQuotient.

  Context `{Univalence} (A : Type).

  Definition trunc_paths_rel : A -> A -> PropU
    := fun x y => ptrunc_PropU (x = y).

  Definition tpr_refl (x : A) : fst (trunc_paths_rel x x) := trunc refl.

  Definition tpr_sym (x y : A)
    : fst (trunc_paths_rel x y) -> fst (trunc_paths_rel y x)
    := ptrunc_rec ptrunc_isProp (fun p => trunc p⁻¹).

  Definition tpr_trans (x y z : A)
    : fst (trunc_paths_rel x y) -> fst (trunc_paths_rel y z)
      -> fst (trunc_paths_rel x z)
    := fun u v => ptrunc_rec ptrunc_isProp
                    (fun p => ptrunc_rec ptrunc_isProp (fun q => trunc (q ⋅ p)) v) u.

  Definition strunc_quot_paths (x y : A)
    : ((cls trunc_paths_rel x = cls trunc_paths_rel y) -> ptrunc (x = y))
      × (ptrunc (x = y) -> cls trunc_paths_rel x = cls trunc_paths_rel y)
    := cls_eq_iff trunc_paths_rel tpr_refl tpr_sym tpr_trans x y.

  Definition strunc_quot_rec {S : Type} (sS : isSet S) (g : A -> S)
    : quot trunc_paths_rel -> S
    := fbar trunc_paths_rel tpr_refl sS g
         (fun x y => ptrunc_rec (sS _ _) (ap g)).

  Definition strunc_quot_rec_cls {S : Type} (sS : isSet S) (g : A -> S)
    (x : A) : strunc_quot_rec sS g (cls trunc_paths_rel x) = g x := refl.

End SetTruncAsQuotient.

(** Exercise [xca:map-induces-quotient]. *)
Section MapInducesQuotient.

  Context `{Univalence} {A B : Type} (f : A -> B).

  Definition eq_f : A -> A -> PropU := fun a a' => ptrunc_PropU (f a = f a').

  Definition eq_f_refl (a : A) : fst (eq_f a a) := trunc refl.
  Definition eq_f_sym (a a' : A) : fst (eq_f a a') -> fst (eq_f a' a)
    := ptrunc_rec ptrunc_isProp (fun p => trunc p⁻¹).
  Definition eq_f_trans (a a' a'' : A)
    : fst (eq_f a a') -> fst (eq_f a' a'') -> fst (eq_f a a'')
    := fun u v => ptrunc_rec ptrunc_isProp
                    (fun p => ptrunc_rec ptrunc_isProp (fun q => trunc (q ⋅ p)) v) u.

  Definition e_f_resp (a a' : A)
    : fst (eq_f a a') -> (settrunc ∘ im_p f) a = (settrunc ∘ im_p f) a'
    := ptrunc_rec (strunc_isSet _ _)
         (fun p : f a = f a' =>
            ap settrunc (path_sigma_prop (u := im_p f a) (v := im_p f a')
                           (fun _ => ptrunc_isProp) p)).

  Definition e_f : quot eq_f -> strunc (im f)
    := fbar eq_f eq_f_refl strunc_isSet (settrunc ∘ im_p f) e_f_resp.

  Definition e_f_commutes : settrunc ∘ im_p f = e_f ∘ cls eq_f := refl.

  (** Uniqueness of [e_f]. *)
  Definition e_f_unique
    : isContr {g : quot eq_f -> strunc (im f) & settrunc ∘ im_p f = g ∘ cls eq_f}
    := quot_univ_prop eq_f eq_f_refl strunc_isSet (settrunc ∘ im_p f) e_f_resp.

  Definition e_f_inv : strunc (im f) -> quot eq_f.
  Proof.
    refine (strunc_rec (quot_isSet eq_f) _). intro w.
    refine (@wconst_elim _ _ (fun v : fiber f (fst w) => cls eq_f (fst v))
              (quot_isSet eq_f) _ (snd w)).
    intros [a e] [a' e'].
    exact (snd (cls_eq_iff eq_f eq_f_refl eq_f_sym eq_f_trans a a')
             (trunc (e' ⋅ e⁻¹))).
  Defined.

  Definition e_f_isEquiv : isEquiv e_f.
  Proof.
    refine (iso_to_isEquiv e_f e_f_inv _ _).
    - refine (im_ind eq_f _ (fun z => quot_isSet eq_f _ _) _). intro a.
      exact refl.
    - refine (strunc_ind_prop _ (fun w => strunc_isSet _ _) _).
      intros [y u]. revert u.
      refine (ptrunc_ind _ (fun _ => strunc_isSet _ _) _).
      intros [a e]. revert y e. refine (paths_ind_r _ _ _). exact refl.
  Defined.

End MapInducesQuotient.

(** * Part 7: Sections 2.23 - 2.24

    ** Summary of this formalization

    Sections 2.23 - 2.24 are formalized in this file, which builds on
    [IntroUF.v] - [IntroUF6.v] and [Bridge.v].  It compiles, with nothing
    admitted.  [Print Assumptions]: the pigeonhole principle uses no
    axioms; [Funext] and [Univalence] are used only where needed.

    Book notions defined from Coq-HoTT notions: [pred :≡ nat_pred], and
    [Fin] is the library's [Fin] (same name; [Fin(succ(n)) ≡ Succ(Fin(n))]
    by definition).  Own definitions: [le], [lt] (the book's
    [m ≤ n :≡ ∑_k (k + m = n)], equivalent to the library's inductive
    [<=], [<], whose lemmas we reuse), [Pmin], [μ_P] ([mu]), [Succ]
    ([SuccT]), [isFinSet], [FinSet], [FinSet_n], [Card], [lookup].

    2.23 More on natural numbers
    - [≤] and [<] are propositions; exercise [xca:try-your-luck-N]
      (injectivity of [succ], commutativity, associativity and
      distributivity, transitivity, monotonicity, [≤] iff [<] or [=],
      antisymmetry, asymmetry of [<]).
    - [lem:dec-eq+order-N], and [ℕ] is a set by Hedberg's theorem.
    - [def:Nwellordered]: bounded search [μ_P] as in the book, its
      correctness, and [min(P)] for decidable [P] that merely has a
      witness.
    - [lem:PHP], with explicit witnesses; the proof searches first for a
      collision with [f(N+1)] and only otherwise uses the book's [g].
    - [cor:Fin-n-injective], derived from [Fin(m) = Fin(n) → m = n]
      (library [nat_eq_fin_equiv]) instead of from PHP.
    - [lem:euclid-div] as contractibility of the type of quotients and
      remainders, using the library's division instead of bounded search.

    2.24 The type of finite sets
    - Exercise [xca:finite-types]: the elements of [Fin 0], [Fin 1],
      [Fin 2]; [Fin 1 ≃ True], [Fin 2 ≃ Bool]; [Fin(n) ≃ ∑_k (k < n)] (via
      the library's [equiv_fin_finnat]); [Fin m = Fin n → m = n].
    - [isFinSet], [lem:maxonefinitetype], [FinSet], [FinSet_n], [Card];
      [FinSet ≃ ∑_n FinSet_n]; [FinSet_0] and [FinSet_1] are contractible.
    - Exercise [xca:finsets-decidable].
    - Exercise [xca:2-element-sets]: [T = T] is a 2-element set;
      [¬ ∏_{T : FinSet_2} (T = 𝟚)] (by univalence); and, uniformly in
      [T : FinSet_2], [(T = T) = 𝟚] ([two_element_loops_Bool]: a loop is
      sent to [yes] iff it is [refl], which is decidable) and
      [T = (𝟚 = T)] ([two_element_paths_Bool]: [t] gives the equivalence
      [yes ↦ t], [no ↦] the other element).
      NOTE for the book text, following a hint by the author: the last
      two parts first show that [∑_{x:T} ¬(x = t)] is a proposition for
      [t : T] ([compl_isProp]), so that "the other element" of [t] is
      well defined without choice ([other]); and they repeatedly use
      that, to prove a proposition about all [T : FinSet_2], one may
      assume [T ≡ 𝟚] ([FinSet2_prop_ind], since [FinSet_2] is connected).
      The book could give these two hints with the exercise.
    - Exercise [xca:tabulation] ([lookup]) and [cor:lists-truncated].
    - Remark [rem:subset-of-fin-set]: a proposition is a finite set iff
      it is decidable.
    - Exercise [xca:dec-quant-finset].
    - Exercise [xca:fin-sum-of-finsets] and exercise
      [xca:dec-quot-finite-set], via a bridge between [isFinSet] and the
      library's class [Finite] ([finite_sigma], [fcard_prod], [finadd],
      [finite_quotient]).

    From 2.22
    - Exercise [xca:ints-as-quotient], placed here since it uses the
      results on [ℕ] of 2.23: [ints_quot_Z : A/R ≃ Z] for
      [A :≡ ℕ × ℕ], [R((w₁,d₁),(w₂,d₂)) :≡ (w₁ + d₂ = w₂ + d₁)] and
      [Z :≡ {(w,d) | (d = 0) ∨ (w = 0 ∧ d ≠ 0)}], with
      [f([(w,d)]) = (w,d)] for [(w,d,p) : Z] ([intsZ_cls]).  Following a
      hint by the author, [f] is induced by the normal form [nf], sending
      [(w,d)] to [(w - d, 0)] if [w ≥ d] and to [(0, d - w)] otherwise
      (decided by the library's [leq_dichotomy]).  Key facts: [R(x, nf(x))]
      ([RZ_nf]), and elements of [Z] related by [R] are equal
      ([NF_unique]); [f] respects [R] by transitivity of [R].
      NOTE for the book text: the author's hint could be added to the
      exercise.

    Elsewhere
    - The remark that [FinSet] is essentially small is formalized in
      [IntroUF8.v] ([FinSet_essSmall]).

    ** Conventions

    Continuation of [IntroUF.v] - [IntroUF6.v] and [Bridge.v], with the
    same conventions: path composition [q ⋅ p :≡ p ∙ q], fibers with
    [y = f x], and notions that occur definitionally in Coq-HoTT defined
    from the library notion and used under the book's name.  Results that
    need univalence assume Coq-HoTT's [Univalence].

    The library's order [leq] on [nat] is an inductive family, whereas
    the book defines [m ≤ n :≡ ∑_k (k + m = n)]; we use the book's
    definitions [le], [lt] and prove them equivalent to the library's
    [<=] and [<] (written with [%nat]), whose lemmas we then reuse. *)

(** ** 2.23 More on natural numbers *)

Definition ℕ_isSet : isSet ℕ := IsHSet_isSet ishset_nat.

(** The predecessor [pred(0) :≡ 0], [pred(succ(n)) :≡ n] is the library's
    [nat_pred]. *)
Definition pred : ℕ -> ℕ := nat_pred.

Definition pred_0 : pred 0%nat = 0%nat := refl.
Definition pred_succ (n : ℕ) : pred (succ n) = n := refl.

(** Definition [def:orderonN]. *)
Definition le (m n : ℕ) : Type := {k : ℕ & add k m = n}.
Definition lt (m n : ℕ) : Type := {k : ℕ & (add k m = n) × (k ≠ 0%nat)}.

(** Comparison with the library's order. *)
Definition le_leq {m n : ℕ} (h : le m n) : (m <= n)%nat
  := trp (fun t => (m <= t)%nat) (snd h) (leq_add_r m (fst h)).

Definition leq_le {m n : ℕ} (h : (m <= n)%nat) : le m n
  := let w := equiv_leq_add m n h in (fst w; nat_add_comm m (fst w) @ snd w).

Definition lt_ltlib {m n : ℕ} (h : lt m n) : (m < n)%nat.
Proof.
  destruct h as [k [e nz]]. destruct k as [|k].
  - destruct (nz refl).
  - apply (trp (fun t => (m < t)%nat) e).
    exact (trp (fun t => (S m <= t)%nat) (nat_add_succ_r m k)^
             (leq_succ (leq_add_r m k))).
Defined.

Definition ltlib_lt {m n : ℕ} (h : (m < n)%nat) : lt m n.
Proof.
  destruct (equiv_leq_add (S m) n h) as [k e].
  refine (S k; (_; fun z => zero_ne_succ k z⁻¹)).
  exact (nat_add_succ_r m k @ ap S (nat_add_comm m k) @ (nat_add_succ_r k m)^ @ e).
Defined.

(** Both [m ≤ n] and [m < n] are propositions. *)
Definition le_isProp (m n : ℕ) : isProp (le m n).
Proof.
  intros [k e] [k' e'].
  apply (path_sigma_prop (fun _ => ℕ_isSet _ _)).
  exact (isinj_nat_add_l m k k' (e @ e'^)).
Defined.

Definition lt_isProp `{Funext} (m n : ℕ) : isProp (lt m n).
Proof.
  intros [k [e nz]] [k' [e' nz']].
  apply (path_sigma_prop (fun k => prod_isProp (ℕ_isSet _ _) (neg_isProp _))).
  exact (isinj_nat_add_l m k k' (e @ e'^)).
Defined.

(** Exercise [xca:try-your-luck-N]. *)
Section TryYourLuck.

  Definition succ_inj {n m : ℕ}
    : ((succ n = succ m) -> n = m) × (n = m -> succ n = succ m)
    := (path_nat_succ n m; ap succ).

  Definition add_comm (n m : ℕ) : add n m = add m n := nat_add_comm m n.

  Definition add_assoc (n m k : ℕ) : add n (add m k) = add (add n m) k
    := (nat_add_assoc k m n)^.

  Definition mul_comm (n m : ℕ) : mul n m = mul m n := nat_mul_comm n m.

  Definition mul_assoc (n m k : ℕ) : mul n (mul m k) = mul (mul n m) k
    := nat_mul_assoc n m k.

  Definition mul_add_distr (m n k : ℕ)
    : mul m (add n k) = add (mul m n) (mul m k)
    := nat_dist_l m k n.

  Definition le_trans {m n k : ℕ} (h : le m n) (h' : le n k) : le m k
    := leq_le (leq_trans (le_leq h) (le_leq h')).

  Definition lt_trans' {m n k : ℕ} (h : lt m n) (h' : lt n k) : lt m k
    := ltlib_lt (lt_trans (lt_ltlib h) (lt_ltlib h')).

  Definition le_add {m n : ℕ} (p : ℕ) (h : le m n) : le (add m p) (add n p)
    := leq_le (nat_add_l_monotone p (le_leq h)).

  Definition lt_add {m n : ℕ} (p : ℕ) (h : lt m n) : lt (add m p) (add n p)
    := ltlib_lt (nat_add_l_strictly_monotone p (lt_ltlib h)).

  Definition le_mul {m n : ℕ} (p : ℕ) (h : le m n) : le (mul m p) (mul n p)
    := leq_le (nat_mul_r_monotone p (le_leq h)).

  Definition le_refl (n : ℕ) : le n n := (0%nat; nat_add_zero_r n).

  Definition le_iff_lt_or_eq (m n : ℕ)
    : (le m n -> lt m n ⨿ (m = n)) × (lt m n ⨿ (m = n) -> le m n).
  Proof.
    split.
    - intros [k e]. destruct k as [|k].
      + exact (inr ((nat_add_zero_r m)^ @ e)).
      + exact (inl (S k; (e; fun z => zero_ne_succ k z⁻¹))).
    - intros [[k [e _]]|e].
      + exact (k; e).
      + exact (0%nat; nat_add_zero_r m @ e).
  Defined.

  Definition le_antisym (m n : ℕ)
    : (le m n × le n m -> m = n) × (m = n -> le m n × le n m)
    := (fun h => leq_antisym (le_leq (fst h)) (le_leq (snd h));
        fun e => match e with refl => (le_refl m; le_refl m) end).

  Definition lt_asym (m n : ℕ) : ¬ (lt m n × lt n m)
    := fun h => lt_irrefl m (lt_trans (lt_ltlib (fst h)) (lt_ltlib (snd h))).

End TryYourLuck.

(** Lemma [lem:dec-eq+order-N]. *)
Definition eq_dec (n m : ℕ) : isDecidable (n = m) := dec_paths n m.

Definition le_dec (m n : ℕ) : isDecidable (le m n)
  := match dec (m <= n)%nat with
     | inl h => inl (leq_le h)
     | inr nh => inr (fun l => nh (le_leq l))
     end.

Definition lt_dec (m n : ℕ) : isDecidable (lt m n)
  := match dec (m < n)%nat with
     | inl h => inl (ltlib_lt h)
     | inr nh => inr (fun l => nh (lt_ltlib l))
     end.

(** By Hedberg's theorem, [ℕ] is a (decidable) set. *)
Definition ℕ_isDecSet : isDecSet ℕ := hedberg eq_dec.

(** Construction [def:Nwellordered]: the least number principle for
    decidable, non-empty subsets of [ℕ], by bounded search [μ_P]. *)
Section LeastNumber.

  Context (P : ℕ -> PropU) (d : forall n, isDecidable (fst (P n))).

  Definition Pmin (n : ℕ) : Type
    := fst (P n) × (forall m, fst (P m) -> le n m).

  (** Bounded search: [μ_P(0) :≡ 0]; [μ_P(succ(n)) :≡ μ_P(n)] if
      [μ_P(n) < n], and otherwise [n] if [P(n)] and [succ(n)] if not. *)
  Fixpoint mu (n : ℕ) : ℕ
    := match n with
       | O => O
       | S n' => match dec (mu n' < n')%nat with
                 | inl _ => mu n'
                 | inr _ => match d n' with
                            | inl _ => n'
                            | inr _ => S n'
                            end
                 end
       end.

  Definition mu_spec1 (n : ℕ)
    : (mu n <= n)%nat × ((mu n < n)%nat -> fst (P (mu n))).
  Proof.
    induction n as [|n IH].
    - exact (leq_refl 0; fun l => match lt_irrefl 0 l with end).
    - cbn. destruct (dec (mu n < n)%nat) as [l|nl].
      + exact (leq_trans (fst IH) (leq_succ_r (leq_refl n)); fun _ => snd IH l).
      + destruct (d n) as [p|np].
        * exact (leq_succ_r (leq_refl n); fun _ => p).
        * exact (leq_refl (S n); fun l => match lt_irrefl _ l with end).
  Defined.

  Definition mu_spec2 (n m : ℕ) (pm : fst (P m)) : (mu n <= m)%nat.
  Proof.
    induction n as [|n IH].
    - exact (leq_zero_l m).
    - cbn. destruct (dec (mu n < n)%nat) as [l|nl].
      + exact IH.
      + assert (e : mu n = n)
          by exact (leq_antisym (fst (mu_spec1 n)) (Overture.fst leq_iff_not_gt nl)).
        assert (le_nm : (n <= m)%nat) by exact (trp (fun t => (t <= m)%nat) e IH).
        destruct (d n) as [p|np].
        * exact le_nm.
        * assert (ne : n <> m) by (intro q; destruct q; exact (np pm)).
          destruct (Overture.fst neq_iff_lt_or_gt ne) as [lt_nm|gt_nm].
          -- exact lt_nm.
          -- destruct (lt_irrefl _ (lt_leq_lt_trans le_nm gt_nm)).
  Defined.

  Definition mu_Pmin (n : ℕ) (p : fst (P n)) : Pmin (mu (S n))
    := (snd (mu_spec1 (S n)) (leq_succ (mu_spec2 (S n) n p));
        fun m pm => leq_le (mu_spec2 (S n) m pm)).

  Definition Pmin_isProp `{Funext} : isProp {n : ℕ & Pmin n}.
  Proof.
    intros [n [p h]] [n' [p' h']].
    apply (path_sigma_prop (fun n => prod_isProp (snd (P n))
             (Pi_isProp (fun m => fun_isProp (le_isProp n m))))).
    exact (leq_antisym (le_leq (h n' p')) (le_leq (h' n p))).
  Defined.

  Definition min `{Funext} : ptrunc {n : ℕ & fst (P n)} -> {n : ℕ & Pmin n}
    := ptrunc_rec Pmin_isProp (fun w => (mu (S (fst w)); mu_Pmin (fst w) (snd w))).

End LeastNumber.

(** Remark [rem:computations-can-decide]: decisions are used in
    computations, e.g. [dec (mu n < n)] above. *)

(** Bounded search for a decidable property. *)
Definition lt_succ_cases {k b : ℕ} (l : (k < S b)%nat) : (k < b)%nat ⨿ (k = b).
Proof.
  pose (l' := leq_pred' l : (k <= b)%nat).
  destruct (dec_paths k b) as [e|ne].
  - exact (inr e).
  - destruct (Overture.fst neq_iff_lt_or_gt ne) as [lt_kb|gt_kb].
    + exact (inl lt_kb).
    + destruct (lt_irrefl _ (lt_leq_lt_trans l' gt_kb)).
Defined.

Definition bounded_dec (Q : ℕ -> Type) (dq : forall k, isDecidable (Q k))
  : forall b : ℕ, {k : ℕ & (k < b)%nat × Q k} ⨿ (forall k, (k < b)%nat -> ¬ Q k).
Proof.
  intro b. induction b as [|b IH].
  - right. intros k l. destruct (not_lt_zero_r k l).
  - destruct IH as [[k [l q]]|nq].
    + left. exact (k; (lt_trans l (leq_refl (S b)); q)).
    + destruct (dq b) as [q|nq'].
      * left. exact (b; (leq_refl (S b); q)).
      * right. intros k l.
        destruct (lt_succ_cases l) as [l'|e].
        -- exact (nq k l').
        -- destruct e. exact nq'.
Defined.

(** Lemma [lem:PHP], the pigeonhole principle.  We produce the witnesses
    explicitly.  The proof differs slightly from the book's: we first
    search for an [n < N+1] with [f(n) = f(N+1)], and only otherwise
    apply the induction hypothesis to the book's [g]. *)
Definition PHP_lib (N : ℕ) (f : ℕ -> ℕ)
  (hf : forall n, (n < S N)%nat -> (f n < N)%nat)
  : {m : ℕ & {n : ℕ & (m < n)%nat × ((n < S N)%nat × (f n = f m))}}.
Proof.
  revert f hf. induction N as [|N IH]; intros f hf.
  - destruct (not_lt_zero_r _ (hf 0%nat (leq_refl 1))).
  - destruct (bounded_dec (fun k => f k = f (S N)) (fun k => dec_paths _ _) (S N))
      as [[k [lk ek]]|nc].
    + exact (k; (S N; (lk; (leq_refl (S (S N)); ek⁻¹)))).
    + pose (g := fun k => match dec_paths (f k) N with
                          | inl _ => f (S N)
                          | inr _ => f k
                          end).
      assert (hfSN : (f (S N) < S N)%nat) by exact (hf (S N) (leq_refl _)).
      assert (hg : forall k, (k < S N)%nat -> (g k < N)%nat).
      { intros k lk. unfold g. destruct (dec_paths (f k) N) as [e|ne].
        - destruct (lt_succ_cases hfSN) as [l|e2].
          + exact l.
          + destruct (nc k lk (e @ e2^)).
        - destruct (lt_succ_cases (hf k (lt_trans lk (leq_refl _)))) as [l|e2].
          + exact l.
          + destruct (ne e2). }
      destruct (IH g hg) as [m [n [lmn [ln e]]]].
      refine (m; (n; (lmn; (lt_trans ln (leq_refl _); _)))).
      unfold g in e.
      destruct (dec_paths (f n) N) as [en|nen], (dec_paths (f m) N) as [em|nem].
      * exact (en @ em^).
      * destruct (nc m (lt_trans lmn ln) e^).
      * destruct (nc n ln e).
      * exact e.
Defined.

Definition PHP (N : ℕ) (f : ℕ -> ℕ)
  (hf : forall n, lt n (succ N) -> lt (f n) N)
  : {m : ℕ & {n : ℕ & lt m n × (lt n (succ N) × (f n = f m))}}.
Proof.
  destruct (PHP_lib N f (fun n l => lt_ltlib (hf n (ltlib_lt l))))
    as [m [n [lmn [ln e]]]].
  exact (m; (n; (ltlib_lt lmn; (ltlib_lt ln; e)))).
Defined.

(** Exercise [xca:finite-types], part 3: [Fin(n) ≃ ∑_k (k < n)], via the
    library's [equiv_fin_finnat]. *)
Definition Fin_lt_eqv `{Funext} (n : ℕ) : Fin n ≃ {k : ℕ & lt k n}
  := Eqv_comp (Eqv_of_Equiv (equiv_fin_finnat n))
       (tot (fun k (l : (k < n)%nat) => ltlib_lt l);
        tot_isEquiv _ (fun k => snd (Eqv_of_props (IsHProp_isProp (P := (k < n)%nat))
                                       (lt_isProp k n) ltlib_lt lt_ltlib))).

(** Exercise [xca:finite-types], part 4: [Fin m = Fin n] implies [m = n],
    via the library's [nat_eq_fin_equiv]. *)
Definition Fin_paths_eq {m n : ℕ} (e : Fin m = Fin n :> Type) : m = n
  := nat_eq_fin_equiv m n (Equiv_of_Eqv (idtoeqv e)).

(** Corollary [cor:Fin-n-injective].  We derive it from part 4 of
    [xca:finite-types] rather than from the pigeonhole principle. *)
Definition Fin_n_injective `{Funext} {m n : ℕ} (l : lt m n)
  : ({k : ℕ & lt k m} = {k : ℕ & lt k n}) -> False.
Proof.
  intro e.
  pose (E := Eqv_comp (Fin_lt_eqv m) (Eqv_comp (idtoeqv e) (Eqv_inv (Fin_lt_eqv n)))).
  pose (q := nat_eq_fin_equiv m n (Equiv_of_Eqv E)).
  destruct q. exact (lt_irrefl _ (lt_ltlib l)).
Defined.

(** Lemma [lem:euclid-div].  We use the library's division with
    remainder ([nat_div], [nat_mod]) instead of the book's bounded
    search. *)
Definition euclid_div `{Funext} (n m : ℕ) (pos : lt 0%nat m)
  : isContr {q : ℕ & {r : ℕ & lt r m × (n = add (mul q m) r)}}.
Proof.
  pose (pos' := lt_ltlib pos).
  pose (e0 := nat_div_mod_spec n m @ ap (fun t => (t + n mod m)%nat) (nat_mul_comm m _)
              @ nat_add_comm _ _ : n = add (mul (n / m) m) (n mod m)).
  refine ((n / m; (n mod m; (ltlib_lt (nat_mod_lt_r n m pos'); e0)))%nat; _).
  - intros [q [r [l e]]].
    pose (e' := ((nat_div_mod_spec n m)^ @ e
                 @ nat_add_comm _ _ @ ap (fun t => (t + r)%nat) (nat_mul_comm q m))
                : (m * (n / m) + n mod m = m * q + r)%nat).
    destruct (nat_div_mod_unique m _ _ _ _ (nat_mod_lt_r n m pos') (lt_ltlib l) e')
      as [eq er].
    destruct eq, er.
    exact (ap (fun w => ((n / m)%nat; ((n mod m)%nat; w)))
              (prod_isProp (lt_isProp _ _) (ℕ_isSet _ _) _ _)).
Defined.

(** ** 2.24 The type of finite sets *)

(** Definition [def:finiteset]: [Succ(X) :≡ X ⨿ True], and
    [Fin(0) :≡ ∅], [Fin(succ(n)) :≡ Succ(Fin(n))]: this is the library's
    [Fin], which has the same name. *)
Definition SuccT (X : Type) : Type := X ⨿ True.

Definition Fin_0 : Fin 0 = False := refl.
Definition Fin_succ (n : ℕ) : Fin (succ n) = SuccT (Fin n) := refl.

(** Exercise [xca:finite-types], parts 1 and 2. *)
Definition fin1_0 : Fin 1 := inr triv.
Definition fin2_0 : Fin 2 := inl (inr triv).
Definition fin2_1 : Fin 2 := inr triv.

Definition Fin0_elems : Fin 0 -> False := idmap.

Definition Fin1_elems (x : Fin 1) : x = fin1_0
  := match x with inl e => match e with end | inr t => match t with triv => refl end end.

Definition Fin2_elems (x : Fin 2) : (x = fin2_0) ⨿ (x = fin2_1)
  := match x with
     | inl y => inl (ap inl (Fin1_elems y))
     | inr t => inr (match t with triv => refl end)
     end.

Definition Fin1_isProp : isProp (Fin 1)
  := fun x y => (Fin1_elems y)⁻¹ ⋅ Fin1_elems x.

Definition Fin1_True : Fin 1 ≃ True
  := Eqv_of_props Fin1_isProp True_isProp (fun _ => triv) (fun _ => fin1_0).

Definition Fin2_Bool : Fin 2 ≃ Bool.
Proof.
  refine (mkEqv (fun x => match x with inl _ => no | inr _ => yes end)
                (fun b => if b then fin2_1 else fin2_0) _ _).
  - intro x. destruct (Fin2_elems x) as [e|e]; destruct e^; exact refl.
  - intros []; exact refl.
Defined.

(** Definition [def:is-finite]. *)
Definition isFinSet (X : Type) : Type := Ex (fun n : ℕ => X = Fin n).

(** Lemma [lem:maxonefinitetype]. *)
Section MaxOneFiniteType.

  Context {X : Type}.

  Definition card_type : Type := {n : ℕ & ptrunc (X = Fin n)}.

  Definition card_type_isProp : isProp card_type.
  Proof.
    intros [n p] [m q].
    apply (path_sigma_prop (fun _ => ptrunc_isProp)).
    refine (ptrunc_rec (ℕ_isSet _ _) _ p). intro e.
    refine (ptrunc_rec (ℕ_isSet _ _) _ q). intro e'.
    exact (Fin_paths_eq (e' ⋅ e⁻¹)).
  Defined.

  Definition card_type_iff
    : (card_type -> isFinSet X) × (isFinSet X -> card_type)
    := (fun w : card_type =>
          ptrunc_rec ptrunc_isProp
            (fun e : X = Fin (fst w) => trunc ((fst w; e) : {n : ℕ & X = Fin n}))
            (snd w);
        ptrunc_rec card_type_isProp
          (fun w : {n : ℕ & X = Fin n} => (fst w; trunc (snd w)) : card_type)).

End MaxOneFiniteType.

(** Definition [def:groupoidFin]. *)
Definition FinSet : Type := {S : SetU & isFinSet (fst S)}.

Definition FinSet_n (n : ℕ) : Type := {S : SetU & ptrunc (Fin n = fst S :> Type)}.

Definition Card (S : FinSet) : ℕ := fst (snd card_type_iff (snd S)).

Definition Card_spec (S : FinSet) : ptrunc (fst (fst S) = Fin (Card S))
  := snd (snd card_type_iff (snd S)).

(** [FinSet ≃ ∑_{n:ℕ} FinSet_n], by [lem:maxonefinitetype]. *)
Definition FinSet_sum_eqv : FinSet ≃ {n : ℕ & FinSet_n n}.
Proof.
  refine (Eqv_comp (tot (fun S => snd card_type_iff);
                    tot_isEquiv _ (fun S => snd (Eqv_of_props ptrunc_isProp
                                                   card_type_isProp _
                                                   (fst card_type_iff)))) _).
  refine (Eqv_comp (sigma_comm SetU ℕ (fun S n => ptrunc (fst S = Fin n))) _).
  pose (F := fun (n : ℕ) (S : SetU) => Eqv_of_props (ptrunc_isProp (T := fst S = Fin n))
                          (ptrunc_isProp (T := Fin n = fst S :> Type))
                          (ptrunc_rec ptrunc_isProp (fun e => trunc e⁻¹))
                          (ptrunc_rec ptrunc_isProp (fun e => trunc e⁻¹))).
  pose (Fn := fun n => (tot (fun S => fst (F n S)); tot_isEquiv _ (fun S => snd (F n S)))
                       : {S : SetU & ptrunc (fst S = Fin n)} ≃ FinSet_n n).
  exact (tot (fun n => fst (Fn n)); tot_isEquiv _ (fun n => snd (Fn n))).
Defined.

(** [FinSet_0] and [FinSet_1] are contractible. *)
Definition FinSet_0_isContr `{Univalence} : isContr (FinSet_n 0).
Proof.
  refine ((exist (fun X : Type => isSet X) (Fin 0) (prop_is_set False_isProp);
           trunc refl); _).
  intros [[S sS] u].
  apply (path_sigma_prop (fun _ => ptrunc_isProp)).
  apply (path_sigma_prop (fun X => isSet_isProp X)). cbn.
  pose (nS := ptrunc_rec (neg_isProp S)
                (fun e : Fin 0 = S :> Type => fun s => ptoe e⁻¹ s) u).
  exact (etop (Eqv_of_props False_isProp (fun a b => match nS a with end)
                 (fun x => match x with end) (fun s => match nS s with end))).
Defined.

Definition FinSet_1_isContr `{Univalence} : isContr (FinSet_n 1).
Proof.
  refine ((exist (fun X : Type => isSet X) (Fin 1) (prop_is_set Fin1_isProp);
           trunc refl); _).
  intros [[S sS] u].
  apply (path_sigma_prop (fun _ => ptrunc_isProp)).
  apply (path_sigma_prop (fun X => isSet_isProp X)). cbn.
  pose (hs := ptrunc_rec (Sigma_isProp (isProp_isProp S) (fun h => h))
                (fun e : Fin 1 = S :> Type =>
                   ((isProp_Eqv (idtoeqv e) Fin1_isProp; ptoe e fin1_0)
                    : {h : isProp S & S})) u).
  exact (etop (Eqv_of_props Fin1_isProp (fst hs) (fun _ => snd hs) (fun _ => fin1_0))).
Defined.

(** Exercise [xca:finsets-decidable]. *)
Definition isDecSet_isProp `{Funext} (X : Type) : isProp (isDecSet X)
  := Pi_isProp (fun x => Pi_isProp (fun y =>
       Sigma_isProp (isProp_isProp (x = y)) (fun h => lem_isProp h))).

Definition Fin_isDecSet (n : ℕ) : isDecSet (Fin n)
  := hedberg (fun x y => dec_paths x y).

Definition finset_isDecSet `{Funext} {X : Type} (h : isFinSet X) : isDecSet X.
Proof.
  refine (ptrunc_rec (isDecSet_isProp X) _ h). intros [n e].
  exact (trp isDecSet e⁻¹ (Fin_isDecSet n)).
Defined.

(** Exercise [xca:2-element-sets]. *)
Section TwoElementSets.

  Context `{Univalence}.

  (** [Bool = Bool] is equivalent to [Bool] (using [xca:C2]). *)
  Definition BoolPaths_Bool : (Bool = Bool :> Type) ≃ Bool.
  Proof.
    pose (swap_no := ptw (ap fst (ptoe_etop swapEqv)) yes : ptoe swap yes = no).
    pose (back := fun b : Bool => if b then (refl : Bool = Bool :> Type) else swap).
    refine (mkEqv (fun p : Bool = Bool :> Type => ptoe p yes) back _ _).
    - intro p. destruct (Bool_paths_cases p) as [e|e].
      + revert p e. refine (paths_ind_r _ _ _). exact refl.
      + revert p e. refine (paths_ind_r _ _ _). exact (ap back swap_no).
    - intros []; [exact refl | exact swap_no].
  Defined.

  Definition paths_conj_eqv {A B : Type} (e : A = B) : (A = A) ≃ (B = B).
  Proof. destruct e. exact (idEqv _). Defined.

  Definition Fin2_Bool_path : Fin 2 = Bool :> Type := etop Fin2_Bool.

  (** [T = T] is a 2-element set for every 2-element set [T]. *)
  Definition self_paths_two_element (T : FinSet_n 2)
    : isSet (fst (fst T) = fst (fst T))
      × ptrunc (Fin 2 = (fst (fst T) = fst (fst T)) :> Type).
  Proof.
    destruct T as [[X sX] u]. cbn.
    refine (paths_sets_isSet sX; _).
    refine (ptrunc_rec ptrunc_isProp _ u). intro e.
    apply trunc.
    exact (ap (fun Y : Type => Y = Y) e
           ⋅ etop (Eqv_comp Fin2_Bool
                     (Eqv_inv (Eqv_comp (paths_conj_eqv Fin2_Bool_path) BoolPaths_Bool)))).
  Defined.

  (** [¬ ∏_{T : FinSet_2} (T = 𝟚)]: the swap of [Fin 2] gives a loop at
      [Fin 2] in [FinSet_2], along which such a family would have to be
      invariant. *)
  Definition swapFin : Fin 2 -> Fin 2
    := fun x => match x with inl _ => fin2_1 | inr _ => fin2_0 end.

  Definition swapFin_invol (x : Fin 2) : swapFin (swapFin x) = x.
  Proof. destruct (Fin2_elems x) as [e|e]; destruct e^; exact refl. Defined.

  Definition swapFinEqv : Fin 2 ≃ Fin 2
    := mkEqv swapFin swapFin swapFin_invol swapFin_invol.

  Definition swapF : Fin 2 = Fin 2 :> Type := etop swapFinEqv.

  Definition swapF_ne_refl : swapF ≠ refl.
  Proof.
    intro e.
    pose (h := ap fst (ptoe_etop swapFinEqv) : ptoe swapF = swapFin).
    pose (h' := ap ptoe e ⋅ h⁻¹ : swapFin = ptoe (refl (Fin 2 : Type))).
    exact (inl_ne_inr (inr triv) triv (ptw h' fin2_1)).
  Defined.

  Definition Fin2_isSet : isSet (Fin 2) := fun x y => fst (Fin_isDecSet 2 x y).

  Definition Fin2_FinSet2 : FinSet_n 2
    := (exist (fun X : Type => isSet X) (Fin 2) Fin2_isSet; trunc refl).

  Definition cancel_loop {A B : Type} (q : A = A) (x : A = B)
    : trans q⁻¹ x = x -> q = refl.
  Proof.
    destruct x. intro h. exact ((symm_symm q)^ @ ap symm h).
  Defined.

  Definition not_all_two_element_paths
    : ¬ (forall T : FinSet_n 2, fst (fst T) = Fin 2).
  Proof.
    intro s.
    pose (l := path_sigma_prop (u := Fin2_FinSet2) (v := Fin2_FinSet2)
                 (fun _ => ptrunc_isProp)
                 (path_sigma_prop (u := fst Fin2_FinSet2) (v := fst Fin2_FinSet2)
                    (fun X => isSet_isProp X) swapF)).
    pose (a := apD s l).
    assert (t : forall (T T' : FinSet_n 2) (r : T = T') (x : fst (fst T) = Fin 2),
               transport (fun T : FinSet_n 2 => fst (fst T) = Fin 2) r x
               = trans (ap (fun T : FinSet_n 2 => fst (fst T)) r)⁻¹ x).
    { intros T T' r x. destruct r. exact (trans_1p x)⁻¹. }
    assert (ap1 : ap (fun T : FinSet_n 2 => fst (fst T)) l = swapF).
    { refine (ap_compose fst fst l @ _).
      refine (ap (ap fst) (ap_fst_pathpair _ _) @ _).
      exact (ap_fst_pathpair _ _). }
    apply swapF_ne_refl.
    exact (ap1^ @ cancel_loop _ (s Fin2_FinSet2) ((t _ _ l _)^ @ a)).
  Defined.

  (** Exercise [xca:2-element-sets], last two parts, following a hint by
      the author: first show that [∑_{x:T} ¬(x = t)] is a proposition, and
      use that, for propositions, a 2-element set may be assumed to be [𝟚]. *)

  Definition Bool2 : FinSet_n 2
    := (exist (fun X : Type => isSet X) Bool isSet_bool; trunc Fin2_Bool_path).

  (** Every 2-element set is merely equal to [Bool2]. *)
  Definition FinSet2_conn (T : FinSet_n 2) : ptrunc (Bool2 = T).
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ (snd T)). intro e. apply trunc.
    exact (path_sigma_prop (u := Bool2) (v := T) (fun _ => ptrunc_isProp)
             (path_sigma_prop (u := fst Bool2) (v := fst T)
                (fun X => isSet_isProp X) (e ⋅ Fin2_Bool_path⁻¹))).
  Defined.

  (** To prove a proposition about all 2-element sets, we may assume
      that the 2-element set is [Bool]. *)
  Definition FinSet2_prop_ind (P : FinSet_n 2 -> Type)
    (hP : forall T, isProp (P T)) (b : P Bool2) (T : FinSet_n 2) : P T
    := ptrunc_rec (hP T) (fun e => trp P e b) (FinSet2_conn T).

  Definition Bool_compl (t x : Bool) : x ≠ t -> x = negb t.
  Proof.
    destruct t, x; intro n;
      solve [exact refl | destruct (n refl)].
  Defined.

  Definition negb_ne (t : Bool) : negb t ≠ t.
  Proof. destruct t; intro e; [exact (yes_ne_no e⁻¹) | exact (yes_ne_no e)]. Defined.

  (** For [t : T], the complement [∑_{x:T} ¬(x = t)] is a proposition. *)
  Definition compl_isProp (T : FinSet_n 2) (t : fst (fst T))
    : isProp {x : fst (fst T) & x ≠ t}.
  Proof.
    revert t.
    refine (FinSet2_prop_ind (fun T => forall t : fst (fst T), isProp {x : fst (fst T) & x ≠ t})
              (fun T => Pi_isProp (fun t => isProp_isProp _)) _ T).
    intros t [x f] [y g].
    apply (path_sigma_prop (fun _ => neg_isProp _)).
    exact (Bool_compl t x f @ (Bool_compl t y g)⁻¹).
  Defined.

  (** Hence it is contractible, its center being "the other element". *)
  Definition compl (T : FinSet_n 2) : forall t : fst (fst T), {x : fst (fst T) & x ≠ t}
    := FinSet2_prop_ind (fun T => forall t : fst (fst T), {x : fst (fst T) & x ≠ t})
         (fun T => Pi_isProp (compl_isProp T)) (fun t => (negb t; negb_ne t)) T.

  Definition other (T : FinSet_n 2) (t : fst (fst T)) : fst (fst T) := fst (compl T t).

  Definition other_ne (T : FinSet_n 2) (t : fst (fst T)) : other T t ≠ t
    := snd (compl T t).

  Definition other_unique (T : FinSet_n 2) {t x : fst (fst T)} (n : x ≠ t)
    : x = other T t
    := ap fst (compl_isProp T t (x; n) (compl T t)).

  (** Last part: [∏_{T:FinSet_2} (T = (𝟚 = T))].  An element [t] gives the
      equivalence [𝟚 ≃ T] mapping [yes] to [t] and [no] to the other element. *)
  Definition pick (T : FinSet_n 2) (t : fst (fst T)) : Bool -> fst (fst T)
    := fun b => if b then t else other T t.

  Definition pick_isEquiv (T : FinSet_n 2) (t : fst (fst T)) : isEquiv (pick T t).
  Proof.
    revert t.
    refine (FinSet2_prop_ind (fun T => forall t, isEquiv (pick T t))
              (fun T => Pi_isProp (fun t => isEquiv_isProp _)) _ T).
    intro t.
    assert (h : (fun b : Bool => if b then t else negb t) = pick Bool2 t).
    { apply ptw_inv. intros []; [exact refl | exact (other_unique Bool2 (negb_ne t))]. }
    refine (trp isEquiv h _).
    pose (inv := fun b : Bool => if b then t else negb t).
    refine (iso_to_isEquiv inv inv _ _);
      intro b; destruct t, b; exact refl.
  Defined.

  Definition pickEqv (T : FinSet_n 2) (t : fst (fst T)) : Bool ≃ fst (fst T)
    := (pick T t; pick_isEquiv T t).

  Definition Eqv_inj {X Y : Type} (e : X ≃ Y) {x x' : X} : fst e x = fst e x' -> x = x'
    := fun p => (eqinv_l (snd e) x)^ @ ap (eqinv (snd e)) p @ eqinv_l (snd e) x'.

  Definition elems_Bool_Eqv (T : FinSet_n 2) : fst (fst T) ≃ (Bool ≃ fst (fst T)).
  Proof.
    refine (mkEqv (pickEqv T) (fun e => fst e yes) (fun t => refl) _).
    intro e. apply path_Eqv, ptw_inv. intros [].
    - exact refl.
    - exact (other_unique T (fun p => yes_ne_no (Eqv_inj e p)^))^.
  Defined.

  Definition two_element_paths_Bool (T : FinSet_n 2)
    : fst (fst T) = (Bool = fst (fst T) :> Type) :> Type
    := etop (Eqv_comp (elems_Bool_Eqv T) (Eqv_inv (idtoeqv; ua Bool (fst (fst T))))).

  (** Third part: [∏_{T:FinSet_2} ((T = T) = 𝟚)].  A loop [p : T = T] is
      sent to [yes] iff [p = refl], which is decidable. *)
  Definition swap_ne_refl : swap ≠ refl := fun e => refl_ne_swap e⁻¹.

  Definition loop_refl_dec (T : FinSet_n 2) (p : fst (fst T) = fst (fst T))
    : (p = refl) ⨿ ¬ (p = refl).
  Proof.
    revert p.
    refine (FinSet2_prop_ind
              (fun T => forall p : fst (fst T) = fst (fst T), (p = refl) ⨿ ¬ (p = refl))
              (fun T => Pi_isProp (fun p => lem_isProp
                                            (paths_sets_isSet (snd (fst T)) p refl))) _ T).
    intro p. destruct (Bool_paths_cases p) as [e|e].
    - exact (inl e).
    - exact (inr (fun e' => swap_ne_refl (e' ⋅ e⁻¹))).
  Defined.

  Definition loop_Bool (T : FinSet_n 2) (p : fst (fst T) = fst (fst T)) : Bool
    := match loop_refl_dec T p with inl _ => yes | inr _ => no end.

  Definition loop_Bool_isEquiv (T : FinSet_n 2) : isEquiv (loop_Bool T).
  Proof.
    refine (FinSet2_prop_ind (fun T => isEquiv (loop_Bool T))
              (fun T => isEquiv_isProp _) _ T).
    assert (h : (fun p : Bool = Bool :> Type => fst BoolPaths_Bool p) = loop_Bool Bool2).
    { apply ptw_inv. intro p. unfold loop_Bool.
      destruct (loop_refl_dec Bool2 p) as [e|n];
        destruct (Bool_paths_cases p) as [e'|e'].
      - exact (ap (fun q => fst BoolPaths_Bool q) e').
      - destruct (swap_ne_refl (e ⋅ e'⁻¹)).
      - destruct (n e').
      - exact (ap (fun q => fst BoolPaths_Bool q) e'
               @ ptw (ap fst (ptoe_etop swapEqv)) yes). }
    exact (trp isEquiv h (snd BoolPaths_Bool)).
  Defined.

  Definition two_element_loops_Bool (T : FinSet_n 2)
    : (fst (fst T) = fst (fst T)) = Bool :> Type
    := etop (loop_Bool T; loop_Bool_isEquiv T).

End TwoElementSets.

(** Exercise [xca:tabulation]: [lookup : X^* ≃ ∑_{n:ℕ} (Fin(n) → X)].  A
    list [x ℓ] is sent to [(succ(n), i ↦ …)] where the new element [x] is
    at index [inr(triv)] and the elements of [ℓ] at the indices [inl(i)]. *)
Section Tabulation.

  Context {X : Type}.

  Definition lookup_step (x : X) (w : {n : ℕ & Fin n -> X})
    : {n : ℕ & Fin n -> X}
    := (S (fst w); fun i => match i with inl i' => snd w i' | inr _ => x end).

  Fixpoint lookup (l : X^*) : {n : ℕ & Fin n -> X}
    := match l with
       | nil => (0%nat; fun i : Fin 0 => match i with end)
       | cons x l' => lookup_step x (lookup l')
       end.

  Fixpoint unlookup_n (n : ℕ) : (Fin n -> X) -> X^*
    := match n with
       | O => fun _ => nil
       | S n' => fun f => cons (f (inr triv)) (unlookup_n n' (fun i => f (inl i)))
       end.

  Definition unlookup (w : {n : ℕ & Fin n -> X}) : X^* := unlookup_n (fst w) (snd w).

  Definition lookup_isEquiv `{Funext} : isEquiv lookup.
  Proof.
    refine (iso_to_isEquiv lookup unlookup _ _).
    - intro l. induction l as [|x l IH].
      + exact refl.
      + exact (ap (cons x) IH).
    - intros [n f]. revert f. induction n as [|n IH]; intro f.
      + exact (ap (fun g => (0%nat; g) : {n : ℕ & Fin n -> X})
                  (ptw_inv (fun i : Fin 0 => match i with end))).
      + refine (ap (lookup_step (f (inr triv))) (IH (fun i => f (inl i))) @ _).
        refine (ap (fun g => (S n; g) : {n : ℕ & Fin n -> X}) (ptw_inv _)).
        intros [i|t]; [exact refl | destruct t; exact refl].
  Defined.

  Definition lookup_eqv `{Funext} : X^* ≃ {n : ℕ & Fin n -> X}
    := (lookup; lookup_isEquiv).

End Tabulation.

(** Corollary [cor:lists-truncated]: for [n ≥ 0], lists of [n]-types are
    [n]-types. *)
Definition prop_ntype (n : ℕ) : forall X : Type, isProp X -> is_ntype n X.
Proof.
  induction n as [|n IH]; intros X h.
  - exact (prop_is_set h).
  - exact (fun x y => IH _ (prop_is_set h x y)).
Defined.

Definition set_ntype (n : ℕ) {X : Type} (s : isSet X) : is_ntype n X
  := match n with
     | O => s
     | S n' => fun x y => prop_ntype n' _ (s x y)
     end.

Definition list_ntype `{Funext} (n : ℕ) {X : Type} (h : is_ntype n X)
  : is_ntype n (X^*)
  := is_ntype_Eqv n (Eqv_inv lookup_eqv)
       (Sigma_ntype n (set_ntype n ℕ_isSet) (fun k => fun_ntype n h)).

(** Remark [rem:subset-of-fin-set]: a proposition is a finite set if and
    only if it is decidable. *)
Definition cardF {X : Type} (h : isFinSet X) : ℕ := fst (snd card_type_iff h).

Definition finprop_dec `{Funext} {p : Type} (hp : isProp p) (f : isFinSet p)
  : isDecidable p.
Proof.
  destruct (snd card_type_iff f) as [n u].
  refine (ptrunc_rec (lem_isProp hp) _ u). intro e.
  destruct n as [|n].
  - exact (inr (fun x => ptoe e x)).
  - exact (inl (ptoe e⁻¹ (inr triv))).
Defined.

Definition dec_finprop `{Univalence} {p : Type} (hp : isProp p)
  (d : isDecidable p) : isFinSet p
  := match d with
     | inl x => trunc (1%nat; etop (Eqv_of_props hp Fin1_isProp
                                     (fun _ => fin1_0) (fun _ => x)))
     | inr nx => trunc (0%nat; etop (Eqv_of_props hp False_isProp nx
                                     (fun e => match e with end)))
     end.

(** Exercise [xca:dec-quant-finset]. *)
Definition Fin_dec_quant `{Funext}
  : forall (n : ℕ) (P : Fin n -> PropU) (d : forall x, isDecidable (fst (P x))),
    isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x)).
Proof.
  intro n. induction n as [|n IH]; intros P d.
  - exact (inr (ptrunc_rec False_isProp
                  (fun w : {x : Fin 0 & fst (P x)} => match fst w with end));
           inl (fun x : Fin 0 => match x with end)).
  - destruct (IH (fun x => P (inl x)) (fun x => d (inl x))) as [ex al].
    refine (_; _).
    + destruct (d (inr triv)) as [p|np].
      * exact (inl (trunc (inr triv; p))).
      * destruct ex as [u|nu].
        -- exact (inl (ptrunc_rec ptrunc_isProp
                         (fun w : {x : Fin n & fst (P (inl x))} => trunc ((inl (fst w); snd w)
                                          : {x : Fin (S n) & fst (P x)})) u)).
        -- refine (inr (ptrunc_rec False_isProp _)).
           intros [[x|t] q].
           ++ exact (nu (trunc (x; q))).
           ++ destruct t. exact (np q).
    + destruct (d (inr triv)) as [p|np].
      * destruct al as [a|na].
        -- refine (inl _). intros [x|t].
           ++ exact (a x).
           ++ destruct t. exact p.
        -- exact (inr (fun h : forall x, fst (P x) => na (fun x => h (inl x)))).
      * exact (inr (fun h : forall x, fst (P x) => np (h (inr triv)))).
Defined.

Definition dec_quant_path `{Funext} {X : Type} {n : ℕ} (e : X = Fin n :> Type)
  : forall (P : X -> PropU) (d : forall x, isDecidable (fst (P x))),
    isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x)).
Proof. revert X e. refine (paths_ind_r _ _ _). exact (Fin_dec_quant n). Defined.

Definition finset_dec_quant `{Funext} {X : Type} (h : isFinSet X)
  (P : X -> PropU) (d : forall x, isDecidable (fst (P x)))
  : isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x))
  := ptrunc_rec (prod_isProp (lem_isProp ptrunc_isProp)
                   (lem_isProp (Pi_isProp (fun x => snd (P x)))))
       (fun w => dec_quant_path (snd w) P d) h.

(** Finite sets in the book's sense versus Coq-HoTT's class [Finite]. *)
Definition isFinSet_Finite `{Univalence} {X : Type} (h : isFinSet X) : Finite X
  := ptrunc_rec (@IsHProp_isProp _ (ishprop_finite X))
       (fun w => Build_Finite X (fst w) (tr (Equiv_of_Eqv (idtoeqv (snd w))))) h.

Definition Finite_isFinSet `{Univalence} {X : Type} (F : Finite X) : isFinSet X
  := ptrunc_rec ptrunc_isProp
       (fun e => trunc ((fcard X; etop (Eqv_of_Equiv e)) : {n : ℕ & X = Fin n}))
       (merely_equiv_fin X).

Definition cardF_fcard `{Univalence} {X : Type} (h : isFinSet X)
  : cardF h = @fcard X (isFinSet_Finite h)
  := ptrunc_ind (fun h => cardF h = @fcard X (isFinSet_Finite h))
       (fun _ => ℕ_isSet _ _) (fun w => refl) h.

Definition isFinSet_Eqv `{Univalence} {A B : Type} (e : A ≃ B)
  (h : isFinSet B) : isFinSet A
  := ptrunc_rec ptrunc_isProp
       (fun w => trunc ((fst w; snd w ⋅ etop e) : {n : ℕ & A = Fin n})) h.

(** Exercise [xca:fin-sum-of-finsets]. *)
Definition sum_finsets_isFinSet `{Univalence} {X : Type} (hX : isFinSet X)
  (F : X -> FinSet) : isFinSet {x : X & fst (fst (F x))}
  := Finite_isFinSet (@finite_sigma X (fun x => fst (fst (F x)))
                        (isFinSet_Finite hX) (fun x => isFinSet_Finite (snd (F x)))).

Definition card_sum_const `{Univalence} {X Y : Type} (hX : isFinSet X)
  (hY : isFinSet Y) (F : X -> Type) (e : forall x, F x ≃ Y)
  (hS : isFinSet {x : X & F x})
  : cardF hS = mul (cardF hX) (cardF hY).
Proof.
  pose (FX := isFinSet_Finite hX). pose (FY := isFinSet_Finite hY).
  pose (FS := isFinSet_Finite hS).
  pose (E := Eqv_comp (tot (fun x => fst (e x)); tot_isEquiv _ (fun x => snd (e x)))
               (binprod_prod X Y)).
  refine (cardF_fcard hS @ _ @ (ap011 nat_mul (cardF_fcard hX) (cardF_fcard hY))^).
  exact (@fcard_equiv' _ _ (Equiv_of_Eqv E) FS (@finite_prod X Y FX FY)
         @ @fcard_prod X Y FX FY).
Defined.

(** The arithmetical sum [∑_{x:X} f(x)] of [f : X → ℕ] over a finite set,
    via the library's [finadd]. *)
Definition finsum `{Univalence} {X : Type} (h : isFinSet X) (f : X -> ℕ) : ℕ
  := @finadd X (isFinSet_Finite h) f.

(** Exercise [xca:dec-quot-finite-set], via the library's [finite_quotient]
    and [xca:quotients-equivalence]. *)
Definition quot_isFinSet `{Univalence} {X : Type} (hX : isFinSet X)
  (R : X -> X -> PropU)
  (rr : forall x, fst (R x x))
  (rs : forall x y, fst (R x y) -> fst (R y x))
  (rt : forall x y z, fst (R x y) -> fst (R y z) -> fst (R x z))
  (dR : forall x y, isDecidable (fst (R x y)))
  : isFinSet (quot R)
  := isFinSet_Eqv (quot_QuotHIT R rr rs rt)
       (Finite_isFinSet (@finite_quotient _ X (isFinSet_Finite hX)
                           (fun x y => fst (R x y))
                           (fun x y => isProp_IsHProp (snd (R x y)))
                           rr rt rs dR)).

(** Exercise [xca:ints-as-quotient] (from 2.22, placed here since it uses
    the results on [ℕ] of 2.23). *)
Section IntsAsQuotient.

  Context `{Univalence}.

  Definition NN : Type := ℕ × ℕ.

  Definition NN_isSet : isSet NN := Sigma_isSet ℕ_isSet (fun _ => ℕ_isSet).

  (** [R((w₁,d₁),(w₂,d₂)) :≡ (w₁ + d₂ = w₂ + d₁)]. *)
  Definition RZ (x y : NN) : PropU
    := ((add (fst x) (snd y) = add (fst y) (snd x)); ℕ_isSet _ _).

  Definition nat_add_swap (a b c : ℕ) : (a + (b + c) = b + (a + c))%nat
    := nat_add_assoc a b c @ ap (fun t => (t + c)%nat) (nat_add_comm a b)
       @ (nat_add_assoc b a c)^.

  Definition RZ_refl (x : NN) : fst (RZ x x) := refl.

  Definition RZ_sym (x y : NN) : fst (RZ x y) -> fst (RZ y x) := fun r => r⁻¹.

  Definition RZ_trans (x y z : NN) : fst (RZ x y) -> fst (RZ y z) -> fst (RZ x z).
  Proof.
    destruct x as [w1 d1], y as [w2 d2], z as [w3 d3].
    change ((d2 + w1 = d1 + w2)%nat -> (d3 + w2 = d2 + w3)%nat
            -> (d3 + w1 = d1 + w3)%nat).
    intros h1 h2. apply (isinj_nat_add_l d2).
    exact (nat_add_swap d2 d3 w1 @ ap (nat_add d3) h1 @ nat_add_swap d3 d1 w2
           @ ap (nat_add d1) h2 @ nat_add_swap d1 d2 w3).
  Defined.

  (** Following a hint by the author: [(w,d)] is sent to [(w - d, 0)] if
      [w ≥ d], and to [(0, d - w)] otherwise. *)
  Definition nf (x : NN) : NN
    := match leq_dichotomy (snd x) (fst x) with
       | inl _ => ((fst x - snd x)%nat; 0%nat)
       | inr _ => (0%nat; (snd x - fst x)%nat)
       end.

  Definition RZ_nf (x : NN) : fst (RZ x (nf x)).
  Proof.
    destruct x as [w d]. unfold nf.
    destruct (leq_dichotomy (snd (w; d)) (fst (w; d))) as [l|l]; unfold RZ; cbn.
    - exact (nat_add_sub_r_cancel l)^.
    - exact (nat_add_sub_l_cancel (leq_succ_l l) @ (nat_add_zero_r d)^).
  Defined.

  (** [Z :≡ {(w,d) | (d = 0) ∨ (w = 0 ∧ d ≠ 0)}]. *)
  Definition isNF (x : NN) : Type := (snd x = 0%nat) ∨ ((fst x = 0%nat) × (snd x ≠ 0%nat)).

  Definition Z : Type := {x : NN & isNF x}.

  Definition Z_isSet : isSet Z := Sigma_isSet NN_isSet (fun _ => prop_is_set ptrunc_isProp).

  Definition nf_isNF (x : NN) : isNF (nf x).
  Proof.
    destruct x as [w d]. unfold nf.
    destruct (leq_dichotomy (snd (w; d)) (fst (w; d))) as [l|l]; apply trunc.
    - exact (inl refl).
    - exact (inr (refl; fun e => lt_irrefl w (leq_trans l (equiv_nat_sub_leq^-1 e)))).
  Defined.

  Definition add_eq_zero (n m : ℕ) : (n + m = 0)%nat -> n = 0%nat.
  Proof. destruct n; intro e; [exact refl | destruct (neq_nat_zero_succ _ e^)]. Defined.

  (** Elements of [Z] related by [R] are equal. *)
  Definition NF_unique (z z' : Z) : fst (RZ (fst z) (fst z')) -> fst z = fst z'.
  Proof.
    destruct z as [[w d] p], z' as [[w' d'] p']. cbn.
    change ((d' + w = d + w')%nat -> ((w; d) : NN) = (w'; d')).
    revert p. refine (ptrunc_rec (fun_isProp (NN_isSet _ _)) _). intro p.
    revert p'. refine (ptrunc_rec (fun_isProp (NN_isSet _ _)) _). intro p'.
    destruct p as [e|[e n]], p' as [e'|[e' n']]; cbn in *.
    - destruct e^, e'^. intro r. exact (ap (fun t => (t; 0%nat) : NN) r).
    - destruct e^, e'^. intro r. destruct (n' (add_eq_zero d' w r)).
    - destruct e^, e'^. intro r. destruct (n (add_eq_zero d w' r^)).
    - destruct e^, e'^. intro r.
      exact (ap (fun t => (0%nat; t) : NN) ((nat_add_zero_r d)^ @ r^ @ nat_add_zero_r d')).
  Defined.

  Definition nfZ (x : NN) : Z := (nf x; nf_isNF x).

  Definition nf_Z (z : Z) : nfZ (fst z) = z
    := path_sigma_prop (fun _ => ptrunc_isProp)
         (NF_unique (nfZ (fst z)) z (RZ_sym _ _ (RZ_nf (fst z)))).

  Definition nfZ_resp (x y : NN) (r : fst (RZ x y)) : nfZ x = nfZ y
    := path_sigma_prop (fun _ => ptrunc_isProp)
         (NF_unique (nfZ x) (nfZ y)
            (RZ_trans _ _ _ (RZ_trans _ _ _ (RZ_sym _ _ (RZ_nf x)) r) (RZ_nf y))).

  (** The equivalence [f : A/R ≃ Z], with [f([(w,d)]) = (w,d)] for
      [(w,d,p) : Z]. *)
  Definition intsZ : quot RZ -> Z := fbar RZ RZ_refl Z_isSet nfZ nfZ_resp.

  Definition intsZ_cls (z : Z) : intsZ (cls RZ (fst z)) = z := nf_Z z.

  Definition ints_quot_Z : quot RZ ≃ Z.
  Proof.
    refine (mkEqv intsZ (fun z => cls RZ (fst z)) _ intsZ_cls).
    refine (im_ind RZ _ (fun q => quot_isSet RZ _ _) _). intro x.
    exact (snd (cls_eq_iff RZ RZ_refl RZ_sym RZ_trans (nf x) x)
             (RZ_sym _ _ (RZ_nf x))).
  Defined.

End IntsAsQuotient.

(** * Part 8: Sections 2.25 - 2.27

    ** Summary of this formalization

    Sections 2.25 - 2.27 are formalized in this file, which builds on
    [IntroUF.v] - [IntroUF7.v] and [Bridge.v].  It compiles, with nothing
    admitted.  [Print Assumptions]: [Funext], [Univalence] and Coq-HoTT's
    [istrunc_truncation] are used only where needed; the replacement
    principle is a hypothesis of [TruncImg_essSmall].

    2.25 Type families and maps
    - [lem:fst-fiber(a)=B(a)] and [lem:sum-of-fibers] (with direct
      inverses instead of [cor:contract-away]); injections into [n]-types
      have [n]-types as domains.
    - [lem:typefamiliesandfibrations]: [preim : ∑_{B:U} (B → A) ≃ (A → U)],
      by univalence, following the book's proof.
    - Exercises [xca:sum-base-path] and [xca:sum-families].
    - Construction [lem:Prop-Set-pointed-families], parts 1 - 4.  Instead
      of transporting along the path induced by [preim], we reindex the
      sum along the equivalence [preim] itself, so that
      [T(preim(B,f)) ≡ ∏_a S(f⁻¹(a))] holds by definition.
    - Corollary [cor:Inj(T)-is-set].
    - The exercise on essentially [U]-small types:
      [(∑_{A:U'} ∑_{X:U} (A ≃ X)) ≃ U], and families of [U]-small types
      versus maps in [U'] with essentially [U]-small fibers.

    2.26 Higher truncations
    - The specification of [def:join-construction-of-truncation], met by
      the library's [Trunc n] with unit [tr]: its universal property with
      respect to [n]-types.
    - The book's join construction, for any truncation level [n]: the
      [n]-truncated identity family [I_n], [‖A‖_{n+1} :≡ im(I_n)] with its
      unit, which is surjective; [‖A‖_{n+1}] is an [(n+1)]-type; the
      equivalence [eq:trunc-path-eq], [‖x = y‖_n ≃ (|x| = |y|)], proved as
      in the book via [(|x| = |y|) ≃ ∏_z (‖x = z‖_n ≃ ‖y = z‖_n)] and going
      backwards at [|refl_y|_n] (with a Yoneda argument for truncated
      identity types); the universal property of [‖A‖_{n+1}], obtained by
      showing that the comparison map from the library's [Trunc (n+1) A]
      is an equivalence (an injective surjection) rather than by the
      book's contractible-extensions argument; and the re-sizing of
      [‖A‖_{n+1}] into the universe of [A] by the replacement principle.

    2.27 Higher structure: stuff, structure, and properties
    - Maps that forget at most [n]-structure, structure, properties, or
      nothing; forgetting properties is being an injection and forgetting
      nothing is being an equivalence, both by definition.
    - The refined image factorization
      [B ≃ ∑_a f⁻¹(a) → ∑_a ‖f⁻¹(a)‖₀ → ∑_a ‖f⁻¹(a)‖ → A], which commutes by
      definition; the fibers of the first map are connected, those of the
      second are nonempty sets (exercise [xca:0Im-to-Im]: the fiber at
      [(a,p)] is [‖f⁻¹(a)‖₀]), and the last map is an injection.
    - Example [exa:stuff-struct-prop]: [fst : FinSet × FinSet → FinSet]
      forgets stuff, [fst : ∑_{A:FinSet} A → FinSet] forgets structure, and
      [FinSet_n → FinSet] forgets properties.
    - Exercise [xca:stuff-struct-prop] (more examples) has no single
      formal statement and is left out.

    Remark after [def:groupoidFin] (from 2.24)
    - [FinSet] is essentially [U]-small ([FinSet_essSmall]), given the
      replacement principle.  NOTE for the book text, following a hint by
      the author: the proof does not go through [FinSet ≃ im(Fin : ℕ → U)]
      as the remark suggests, but uses that, by univalence, a sum over [U]
      such as [FinSet] is locally [U]-small; then replacement applies to
      the surjection [ℕ → FinSet], [n ↦ Fin n], whose image is [FinSet].
      The book could mention this use of univalence explicitly.

    ** Conventions

    Continuation of [IntroUF.v] - [IntroUF7.v] and [Bridge.v], with the
    same conventions: path composition [q ⋅ p :≡ p ∙ q], fibers with
    [y = f x], and notions that occur definitionally in Coq-HoTT defined
    from the library notion and used under the book's name.  Results that
    need univalence assume Coq-HoTT's [Univalence]. *)

(** ** 2.25 Type families and maps *)

(** Lemma [lem:fst-fiber(a)=B(a)]: [e_a(b) :≡ ((a,b), refl_a)].  We give
    the inverse directly instead of using [cor:contract-away]. *)
Definition fst_fiber_eqv {A : Type} (B : A -> Type) (a : A)
  : B a ≃ fiber (@fst A B) a.
Proof.
  refine (mkEqv (fun b => ((a; b); refl))
                (fun w => trp B (snd w)⁻¹ (snd (fst w))) (fun b => refl) _).
  intros [[x b] p]. cbn in p |- *. destruct p. exact refl.
Defined.

(** Lemma [lem:sum-of-fibers]: [e(b,a,p) :≡ a]. *)
Definition sum_of_fibers {A B : Type} (f : A -> B)
  : {b : B & fiber f b} ≃ A.
Proof.
  refine (mkEqv (fun w => fst (snd w)) (fun a => (f a; (a; refl))) _ (fun a => refl)).
  intros [b [a p]]. cbn in p |- *.
  revert b p. refine (paths_ind_r _ _ _). exact refl.
Defined.

(** If [f] is an injection, [A] is an [n]-type when [B] is. *)
Definition inj_ntype (n : ℕ) {A B : Type} {f : A -> B} (j : isInj f)
  (h : is_ntype n B) : is_ntype n A
  := is_ntype_Eqv n (sum_of_fibers f) (subtype_ntype n j h).

(** Lemma [lem:typefamiliesandfibrations]. *)
Section TypeFamiliesAndFibrations.

  Universe u.
  Context `{Univalence} (A : Type@{u}).

  Definition preim (w : {B : Type@{u} & B -> A}) : A -> Type@{u}
    := fun a => fiber (snd w) a.

  Definition preim_inv (C : A -> Type@{u}) : {B : Type@{u} & B -> A}
    := ({a : A & C a}; fst).

  Definition preim_isEquiv : isEquiv preim.
  Proof.
    refine (iso_to_isEquiv preim preim_inv _ _).
    - intros [B f].
      pose (E := sum_of_fibers f).
      refine (pathpair (Y := fun X : Type@{u} => X -> A) (etop E) _).
      refine (trp_fun_dom (etop E) fst @ _).
      apply ptw_inv. intro b. cbn.
      refine (ap fst (trp_inv_eqinv (etop E) E (ap fst (ptoe_etop E)) b) @ _).
      exact (snd (snd (eqinv (snd E) b)) @ ap f (eqinv_r (snd E) b)).
    - intro C. apply ptw_inv. intro a.
      exact (etop (Eqv_inv (fst_fiber_eqv C a))).
  Defined.

  Definition preim_eqv : {B : Type@{u} & B -> A} ≃ (A -> Type@{u})
    := (preim; preim_isEquiv).

End TypeFamiliesAndFibrations.

(** Exercise [xca:sum-base-path]. *)
Definition sum_base_path {X Y : Type} (p : Y = X) (T : X -> Type)
  : {x : X & T x} ≃ {y : Y & T (ptoe p y)}.
Proof. destruct p. exact (idEqv _). Defined.

(** Exercise [xca:sum-families]: an instance of [xca:AC-in-TT]. *)
Definition sum_families (S : Type -> Type) (X : Type)
  : (X -> {Y : Type & S Y}) ≃ {F : X -> Type & forall x, S (F x)}
  := type_theoretic_AC X Type (fun _ Y => S Y).

(** Construction [lem:Prop-Set-pointed-families].  Instead of transporting
    along the path induced by [preim] ([xca:sum-base-path]), we reindex
    the sum along the equivalence [preim] directly, so that
    [T(preim(B,f)) ≡ ∏_a S(f⁻¹(a))] holds by definition. *)
Section FamiliesStructure.

  Universe u.
  Context `{Univalence} (A : Type@{u}).

  Definition families_structure (S : Type@{u} -> Type@{u})
    : (A -> {B : Type@{u} & S B})
      ≃ {B : Type@{u} & {f : B -> A & forall a, S (fiber f a)}}.
  Proof.
    refine (Eqv_comp (sum_families S A) _).
    refine (Eqv_comp (Eqv_inv (Eqv_of_Equiv
              (equiv_functor_sigma_pb (Q := fun F : A -> Type@{u} => forall a, S (F a))
                 (Equiv_of_Eqv (preim_eqv A))))) _).
    exact (Eqv_inv (sigma_assoc Type@{u} (fun B => B -> A)
                      (fun B f => forall a, S (fiber f a)))).
  Defined.

  Definition families_props
    : (A -> {B : Type@{u} & isProp B})
      ≃ {B : Type@{u} & {f : B -> A & forall a, isProp (fiber f a)}}
    := families_structure (fun B => isProp B).

  Definition families_sets
    : (A -> {B : Type@{u} & isSet B})
      ≃ {B : Type@{u} & {f : B -> A & forall a, isSet (fiber f a)}}
    := families_structure (fun B => isSet B).

  Definition families_points
    : (A -> {B : Type@{u} & B})
      ≃ {B : Type@{u} & {f : B -> A & forall a, fiber f a}}
    := families_structure (fun B => B).

  (** Corollary [cor:Inj(T)-is-set]: subtypes correspond to predicates by
      taking fibers, and [Inj(T)] is a set. *)
  Definition Inj_eqv_predicates
    : (A -> {B : Type@{u} & isProp B}) ≃ Inj A
    := families_props.

  Definition Inj_isSet : isSet (Inj A)
    := is_ntype_Eqv 0 Inj_eqv_predicates (Pi_isSet (fun _ => PropU_isSet)).

End FamiliesStructure.

(** Exercise: families of [U]-small types versus maps in [U'] with
    essentially [U]-small fibers. *)
Section EssSmallFamilies.

  Universes u v.
  Constraint u < v.
  Context `{Univalence}.

  Definition Sess (X : Type@{v}) : Type@{v} := {Y : Type@{u} & X ≃ Y}.

  Definition Sess_fiber_isContr (Y : Type@{u}) : isContr {X : Type@{v} & X ≃ Y}
    := isContr_Eqv (tot (fun (X : Type@{v}) (p : X = Y) => idtoeqv p);
                    tot_isEquiv _ (fun X => ua X Y))
                   (singleton_contr' (Y : Type@{v})).

  Definition essSmall_total_eqv : {X : Type@{v} & Sess X} ≃ Type@{u}.
  Proof.
    refine (Eqv_comp (sigma_comm Type@{v} Type@{u} (fun X Y => X ≃ Y)) _).
    refine (mkEqv fst
              (fun Y : Type@{u} =>
                 (Y; exist (fun X : Type@{v} => X ≃ Y) Y (idEqv Y))
                 : {y : Type@{u} & {x : Type@{v} & x ≃ y}})
              _ (fun Y => refl)).
    intros [Y w].
    exact (ap (fun w' => (Y; w')) (isContr_isProp' (Sess_fiber_isContr Y) _ w)).
  Defined.

  Definition small_families_eqv (A : Type@{v})
    : (A -> Type@{u})
      ≃ {B : Type@{v} & {f : B -> A & forall a, Sess (fiber f a)}}
    := Eqv_comp (Pi_eqv (fun _ : A => Eqv_inv essSmall_total_eqv))
         (families_structure A Sess).

End EssSmallFamilies.

(** ** 2.26 Higher truncations *)

(** Construction [def:join-construction-of-truncation], specification:
    for every truncation level [n] the library's [Trunc n] with unit
    [tr] has the universal property with respect to [n]-types. *)
Definition trunc_univ_prop `{Funext} (n : trunc_index) (A B : Type)
  `{IsTrunc n B} : (Trunc n A -> B) ≃ (A -> B)
  := mkEqv (fun h => h ∘ tr) (Trunc_rec)
       (fun h => ptw_inv (Trunc_ind (fun x => Trunc_rec (h ∘ tr) x = h x)
                                    (fun a => refl)))
       (fun g => refl).

(** The book's implementation, the join construction: [‖A‖_{n+1}] is the
    image of the [n]-truncated identity family
    [I_n : A → (A → ∑_{X:U} isnType(X))], [x ↦ (y ↦ ‖x = y‖_n)]. *)
Definition prop_istrunc_succ (n : trunc_index) {X : Type} (h : isProp X)
  : IsTrunc n.+1 X.
Proof. pose proof (isProp_IsHProp h). destruct n as [|m]; exact _. Defined.

Section JoinConstruction.

  Context `{Univalence} (n : trunc_index) (A : Type).

  Definition nType : Type := {X : Type & IsTrunc n X}.

  Definition I_n : A -> A -> nType
    := fun x y => (Trunc n (x = y); istrunc_truncation n _).

  Definition TruncImg : Type := im I_n.

  Definition unitImg : A -> TruncImg := im_p I_n.

  Definition unitImg_def (x : A)
    : unitImg x = (I_n x; trunc (x; refl)) := refl.

  Definition unitImg_isSurj : isSurj unitImg := im_p_isSurj I_n.

  (** [‖A‖_{n+1}] is an [(n+1)]-type, since the type of [n]-types is an
      [(n+1)]-type. *)
  Definition TruncImg_istrunc : IsTrunc n.+1 TruncImg.
  Proof.
    unfold TruncImg, im, Ex, ptrunc, nType.
    assert (h : forall Y : Type, IsTrunc n.+1 (Trunc (-1) Y)).
    { intro Y. destruct n as [|m]; exact _. }
    exact _.
  Defined.

  (** The map [‖x = y‖_n → (|x|_{n+1} = |y|_{n+1})] of equation
      [eq:trunc-path-eq]. *)
  Definition path_img (x y : A) : Trunc n (x = y) -> unitImg x = unitImg y
    := @Trunc_rec n (x = y) _ (@istrunc_paths _ _ TruncImg_istrunc _ _)
         (ap unitImg).

  (** Families of maps out of [‖x = _‖_n] into [n]-types are determined
      by their value at [|refl_x|_n]. *)
  Definition yoneda_trunc {x : A} {T : A -> Type} `{forall z, IsTrunc n (T z)}
    (F G : forall z, Trunc n (x = z) -> T z) (h : F x (tr refl) = G x (tr refl))
    : forall z u, F z u = G z u.
  Proof. intros z u. revert u. refine (Trunc_ind _ _). intro q. destruct q. exact h. Defined.

  (** [(|x| = |y|) ≃ ∏_{z:A} (‖x = z‖_n ≃ ‖y = z‖_n)], as in the book. *)
  Definition Phi_eqv (x y : A)
    : (unitImg x = unitImg y) ≃ (forall z, Trunc n (x = z) ≃ Trunc n (y = z)).
  Proof.
    refine (Eqv_comp (subtype_paths_eqv (fun P => ptrunc_isProp)
                        (unitImg x) (unitImg y)) _).
    refine (Eqv_comp (ptw; funext (I_n x) (I_n y)) _).
    exact (Pi_eqv (fun z => Eqv_comp
             (subtype_paths_eqv (fun X => @IsHProp_isProp (IsTrunc n X) _)
                (I_n x z) (I_n y z))
             (idtoeqv; ua _ _))).
  Defined.

  Let Phi (x y : A) (r : unitImg x = unitImg y) (z : A)
    : Trunc n (x = z) -> Trunc n (y = z)
    := fst (fst (Phi_eqv x y) r z).

  Definition Phi_path_img (x : A)
    : forall y (s : Trunc n (x = y)), Phi x y (path_img x y s) y s = tr refl.
  Proof.
    intros y s. revert s. refine (Trunc_ind _ _). intro p. destruct p. exact refl.
  Defined.

  Definition Phi_path_img_aux (x : A)
    : forall y (r : unitImg x = unitImg y) (s : Trunc n (x = y)),
      Phi x y r y s = tr refl
      -> Phi x y (path_img x y s) x (tr refl) = Phi x y r x (tr refl).
  Proof.
    intros y r s. revert s. refine (Trunc_ind _ _). intro p.
    revert y p r. refine (paths_ind _ _ _). intros r h. exact h^.
  Defined.

  Definition path_img_key (x y : A) (r : unitImg x = unitImg y)
    (s : Trunc n (x = y)) (h : Phi x y r y s = tr refl)
    : path_img x y s = r.
  Proof.
    pose (t := snd (Phi_eqv x y)).
    refine ((eqinv_l t _)^ @ ap (eqinv t) _ @ eqinv_l t r).
    apply ptw_inv. intro z. apply path_Eqv. apply ptw_inv.
    exact (yoneda_trunc (T := fun z => Trunc n (y = z))
             (Phi x y (path_img x y s)) (Phi x y r)
             (Phi_path_img_aux x y r s h) z).
  Defined.

  (** Equation [eq:trunc-path-eq]: [‖x = y‖_n ≃ (|x|_{n+1} = |y|_{n+1})],
      with inverse given by going backwards at [|refl_y|_n]. *)
  Definition path_img_isEquiv (x y : A) : isEquiv (path_img x y).
  Proof.
    pose (psi := fun r => eqinv (snd (fst (Phi_eqv x y) r y)) (tr refl)).
    refine (iso_to_isEquiv (path_img x y) psi _ _).
    - intro s.
      exact ((ap (eqinv (snd (fst (Phi_eqv x y) (path_img x y s) y)))
                 (Phi_path_img x y s))^
             @ eqinv_l (snd (fst (Phi_eqv x y) (path_img x y s) y)) s).
    - intro r.
      exact (path_img_key x y r (psi r) (eqinv_r (snd (fst (Phi_eqv x y) r y)) _)).
  Defined.

  (** The universal property of [‖A‖_{n+1}], by comparison with the
      library's [Trunc (n+1)]. *)
  Definition truncImg_map : Trunc n.+1 A -> TruncImg
    := @Trunc_rec n.+1 A TruncImg TruncImg_istrunc unitImg.

  Definition truncImg_map_isEquiv : isEquiv truncImg_map.
  Proof.
    apply inj_surj_isEquiv.
    - apply ap_isEquiv_isInj.
      pose proof TruncImg_istrunc.
      assert (hP : forall a b : Trunc n.+1 A,
                 IsTrunc n.+1 (isEquiv (@ap _ _ truncImg_map a b)))
        by (intros; exact (prop_istrunc_succ n (isEquiv_isProp _))).
      refine (Trunc_ind _ _). intro x.
      refine (Trunc_ind _ _). intro y.
      pose (pT := equiv_path_Tr (n := n) x y).
      pose (pT' := equiv_inverse pT).
      refine (isEquiv_homotopic (path_img x y ∘ pT')
                (@ap _ _ truncImg_map (tr x) (tr y)) _
                (comp_isEquiv (isEquiv_of_IsEquiv pT') (path_img_isEquiv x y))).
      intro r. refine (_ @ ap (ap truncImg_map) (eisretr pT r)).
      change (path_img x y (pT' r) = ap truncImg_map (pT (pT' r))).
      generalize (pT' r). refine (Trunc_ind _ _). intro p.
      destruct p. exact refl.
    - intro z.
      exact (ptrunc_rec ptrunc_isProp
               (fun w : fiber unitImg z => trunc ((tr (fst w); snd w)
                                                 : fiber truncImg_map z))
               (unitImg_isSurj z)).
  Defined.

  Definition precomp_eqv `{Funext} {X Y Z : Type} (e : X ≃ Y)
    : (Y -> Z) ≃ (X -> Z)
    := mkEqv (fun h => h ∘ fst e) (fun k => k ∘ eqinv (snd e))
         (fun h => ptw_inv (fun y => ap h (eqinv_r (snd e) y)))
         (fun k => ptw_inv (fun x => ap k (eqinv_l (snd e) x))).

  Definition TruncImg_univ_prop (B : Type) `{IsTrunc n.+1 B}
    : (TruncImg -> B) ≃ (A -> B)
    := Eqv_comp (precomp_eqv (truncImg_map; truncImg_map_isEquiv))
         (trunc_univ_prop n.+1 A B).

  Definition TruncImg_univ_prop_map (B : Type) `{IsTrunc n.+1 B}
    (h : TruncImg -> B) : fst (TruncImg_univ_prop B) h = h ∘ unitImg := refl.

End JoinConstruction.

(** Finally, the book re-sizes [‖A‖_{n+1}] into the universe of [A] using
    the replacement principle: maps into the type of [n]-types form a
    locally small type, by univalence. *)
Section JoinResizing.

  Universe u.
  Context `{Univalence} (n : trunc_index) (A : Type@{u}).

  Definition nType_fun_locSmall
    : forall F G : A -> {X : Type@{u} & IsTrunc n X}, {Y : Type@{u} & (F = G) ≃ Y}.
  Proof.
    intros F G.
    refine (exist (fun Y : Type@{u} => (F = G) ≃ Y) (forall z, fst (F z) ≃ fst (G z)) _).
    exact (
           Eqv_comp (ptw; funext F G)
             (Pi_eqv (fun z => Eqv_comp
                (subtype_paths_eqv (fun X => @IsHProp_isProp (IsTrunc n X) _) (F z) (G z))
                (idtoeqv; ua _ _)))).
  Defined.

  Definition TruncImg_essSmall (rep : Replacement)
    : {Y : Type@{u} & TruncImg n A ≃ Y}
    := rep A _ (I_n n A) (small_essSmall A) nType_fun_locSmall.

End JoinResizing.

(** ** 2.27 Higher structure: stuff, structure, and properties *)

Section ForgetfulMaps.

  Context {B A : Type} (f : B -> A).

  Definition forgets_n_structure (n : ℕ) : Type
    := forall a, is_ntype n (fiber f a).
  Definition forgets_structure : Type := forall a, isSet (fiber f a).
  Definition forgets_properties : Type := forall a, isProp (fiber f a).
  Definition forgets_nothing : Type := forall a, isContr (fiber f a).

  (** A map forgets properties iff it is an injection, and nothing iff it
      is an equivalence (both by definition). *)
  Definition forgets_properties_isInj : forgets_properties = isInj f := refl.
  Definition forgets_nothing_isEquiv : forgets_nothing = isEquiv f := refl.

End ForgetfulMaps.

(** Fibers of a totalization. *)
Definition fiber_tot {A : Type} {P Q : A -> Type} (g : forall a, P a -> Q a)
  (a : A) (q : Q a) : fiber (tot g) (a; q) ≃ fiber (g a) q
  := Eqv_comp (fiber_hfiber _ _)
       (Eqv_comp (Eqv_of_Equiv (hfiber_functor_sigma_idmap P Q g a q))
                 (Eqv_inv (fiber_hfiber _ _))).

(** A sum of contractible types is equivalent to its base. *)
Definition sigma_contr_fibers {X : Type} {C : X -> Type}
  (c : forall x, isContr (C x)) : {x : X & C x} ≃ X
  := mkEqv fst (fun x => (x; fst (c x)))
       (fun w => pathpair (Y := C) (y := fst (c (fst w))) (y' := snd w)
                   refl (snd (c (fst w)) (snd w)))
       (fun x => refl).

Definition isConn_Eqv {X Y : Type} (e : X ≃ Y) (c : isConn X) : isConn Y
  := surj_isConn (isEquiv_isSurj (snd e)) c.

(** The refined image factorization of [f : B → A]:
    [B ≃ ∑_a f⁻¹(a) → ∑_a ‖f⁻¹(a)‖₀ → ∑_a ‖f⁻¹(a)‖ → A]. *)
Section RefinedImage.

  Context {B A : Type} (f : B -> A).

  Definition rf0 : B ≃ {a : A & fiber f a} := total_fibers f.

  Definition rf1 : {a : A & fiber f a} -> {a : A & strunc (fiber f a)}
    := tot (fun a => settrunc).

  (** The map [|_|' : ‖X‖₀ → ‖X‖] of exercise [xca:0Im-to-Im]. *)
  Definition trunc' {X : Type} : strunc X -> ptrunc X
    := strunc_rec (prop_is_set ptrunc_isProp) trunc.

  Definition rf2 : {a : A & strunc (fiber f a)} -> {a : A & ptrunc (fiber f a)}
    := tot (fun a => trunc').

  Definition rf3 : {a : A & ptrunc (fiber f a)} -> A := fst.

  (** The factorization holds by definition, and the last two types are the
      book's [0]-image and [(-1)]-image ([im f]). *)
  Definition refined_factorization : f = rf3 ∘ rf2 ∘ rf1 ∘ fst rf0 := refl.

  Definition rf3_im : {a : A & ptrunc (fiber f a)} = im f := refl.

  (** The first map forgets pure higher structure: its fibers are
      connected. *)
  Definition settrunc_fiber_isConn `{Univalence} {X : Type} (z : strunc X)
    : isConn (fiber settrunc z).
  Proof.
    refine (_; _).
    - revert z. refine (strunc_ind_prop _ (fun _ => ptrunc_isProp) _). intro x.
      exact (trunc (x; refl)).
    - intros [x p] [y q].
      refine (ptrunc_rec ptrunc_isProp _
                (equiv_inverse (equiv_path_Tr (n := -1) x y) (q ⋅ p⁻¹))).
      intro r.
      exact (trunc (pathpair r (strunc_isSet z (settrunc y) _ q))).
  Defined.

  Definition rf1_fibers_isConn `{Univalence} (a : A) (z : strunc (fiber f a))
    : isConn (fiber rf1 (a; z))
    := isConn_Eqv (Eqv_inv (fiber_tot (fun a => settrunc) a z))
         (settrunc_fiber_isConn z).

  (** Exercise [xca:0Im-to-Im]: the fiber of the second map at [(a,p)] is
      equivalent to [‖f⁻¹(a)‖₀]: it forgets pure structure (the fibers are
      nonempty sets), and remembers which component of the fiber
      [f⁻¹(a)] we are in. *)
  Definition rf2_fiber_eqv (a : A) (p : ptrunc (fiber f a))
    : fiber rf2 (a; p) ≃ strunc (fiber f a)
    := Eqv_comp (fiber_tot (fun a => trunc') a p)
         (sigma_contr_fibers (fun x => isProp_inhabited_isContr
                                         (prop_is_set ptrunc_isProp _ _)
                                         (ptrunc_isProp _ _))).

  Definition rf2_fibers_isSet (a : A) (p : ptrunc (fiber f a))
    : isSet (fiber rf2 (a; p))
    := is_ntype_Eqv 0 (Eqv_inv (rf2_fiber_eqv a p)) strunc_isSet.

  Definition rf2_fibers_nonempty (a : A) (p : ptrunc (fiber f a))
    : ptrunc (fiber rf2 (a; p))
    := ptrunc_rec ptrunc_isProp
         (fun w => trunc (fst (Eqv_inv (rf2_fiber_eqv a p)) (settrunc w))) p.

  (** The last map forgets at most properties: it is the inclusion of the
      image. *)
  Definition rf3_isInj : isInj rf3 := im_i_isInj f.

End RefinedImage.

(** Example [exa:stuff-struct-prop]. *)
Section Examples.

  Context `{Univalence}.

  Definition FinSet_isGrpd : isGrpd FinSet
    := subtype_ntype 1 (fun S => ptrunc_isProp) SetU_isGrpd.

  (** [fst : FinSet × FinSet → FinSet] forgets [1]-structure (stuff). *)
  Definition fst_FinSet2_forgets_stuff
    : forgets_n_structure (@fst FinSet (fun _ => FinSet)) 1
    := fun S => is_ntype_Eqv 1 (fst_fiber_eqv (fun _ => FinSet) S) FinSet_isGrpd.

  (** [fst : ∑_{A:FinSet} A → FinSet] forgets structure (a point). *)
  Definition fst_pointed_FinSet_forgets_structure
    : forgets_structure (@fst FinSet (fun S => fst (fst S)))
    := fun S => is_ntype_Eqv 0 (fst_fiber_eqv (fun S => fst (fst S)) S)
                  (snd (fst S)).

  (** The inclusion [FinSet_n → FinSet] forgets properties. *)
  Definition FinSet_n_incl (n : ℕ) : FinSet_n n -> FinSet
    := tot (fun (S : SetU) (u : ptrunc (Fin n = fst S :> Type)) =>
              ptrunc_rec ptrunc_isProp
                (fun e => trunc ((n; e⁻¹) : {m : ℕ & fst S = Fin m})) u).

  Definition FinSet_n_incl_forgets_properties (n : ℕ)
    : forgets_properties (FinSet_n_incl n).
  Proof.
    intros [S h].
    refine (isProp_Eqv (Eqv_inv (fiber_tot _ S h)) _).
    exact (Sigma_isProp ptrunc_isProp (fun _ => prop_is_set ptrunc_isProp _ _)).
  Defined.

End Examples.

(** Exercise [xca:stuff-struct-prop] asks for more examples of this kind
    of analysis; it has no single formal statement. *)

(** Remark after [def:groupoidFin]: [FinSet] is essentially [U]-small, by
    the replacement principle applied to the surjection [ℕ → FinSet],
    [n ↦ Fin n]; [FinSet] is locally small by univalence. *)
Section FinSetSmall.

  Universe u.
  Context `{Univalence}.

  (** The image of a surjection is equivalent to its codomain. *)
  Definition im_surj_eqv {X Y : Type} (f : X -> Y) (s : isSurj f) : im f ≃ Y
    := sigma_contr_fibers (fun y => isProp_inhabited_isContr ptrunc_isProp (s y)).

  Definition FinSet_U : Type := {S : {X : Type@{u} & isSet X} & isFinSet (fst S)}.

  Definition FinSet_locSmall
    : forall S T : FinSet_U, {Y : Type@{u} & (S = T) ≃ Y}.
  Proof.
    intros S T.
    refine (exist (fun Y : Type@{u} => (S = T) ≃ Y) (fst (fst S) ≃ fst (fst T)) _).
    refine (Eqv_comp (subtype_paths_eqv (fun _ => ptrunc_isProp) S T) _).
    refine (Eqv_comp (subtype_paths_eqv (fun X => isSet_isProp X) (fst S) (fst T)) _).
    exact (idtoeqv; ua _ _).
  Defined.

  Definition Fin_FinSet (n : ℕ) : FinSet_U
    := exist (fun S : {X : Type@{u} & isSet X} => isFinSet (fst S))
         (exist (fun X : Type@{u} => isSet X) (Fin n) (fun x y => fst (Fin_isDecSet n x y)))
         (trunc (exist (fun m : ℕ => (Fin n : Type@{u}) = Fin m) n refl)).

  Definition Fin_FinSet_isSurj : isSurj Fin_FinSet.
  Proof.
    intros [S h]. revert h.
    refine (ptrunc_ind _ (fun _ => ptrunc_isProp) _). intros [n e].
    exact (trunc (n; path_sigma_prop (u := (S; trunc (n; e)) : FinSet_U) (v := Fin_FinSet n)
                       (fun _ => ptrunc_isProp)
                       (path_sigma_prop (u := S) (v := fst (Fin_FinSet n))
                          (fun X => isSet_isProp X) e))).
  Defined.

  Definition FinSet_essSmall (rep : Replacement) : {Y : Type@{u} & FinSet_U ≃ Y}
    := essSmall_Eqv (Eqv_inv (im_surj_eqv Fin_FinSet Fin_FinSet_isSurj))
         (rep ℕ FinSet_U Fin_FinSet (small_essSmall ℕ) FinSet_locSmall).

End FinSetSmall.
