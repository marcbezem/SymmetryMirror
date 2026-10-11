(** * Formalization of Sections 2.2 - 2.6 of [intro-uf.tex]

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

From HoTT Require Import Basics Spaces.Nat.Core Spaces.Nat.Factorial.

Declare Scope uf_scope.
Delimit Scope uf_scope with uf.
Local Open Scope uf_scope.

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
