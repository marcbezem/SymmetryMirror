(** * Formalization of Sections 2.2 - 2.6 of [intro-uf.tex]

    Chapter 2, "An introduction to univalent mathematics", of the book
    "Symmetry".  We use Rocq with the Coq-HoTT library.

    The book follows Book HoTT with some changes that we make explicit
    here:
    1. Path composition is written in the same order as function
       composition: for [p : a = b] and [q : b = c] the book writes
       [p ∙ q], or [q · p], or [q ∘ p].  We define [trans p q] following
       the book (by induction on [q]) and use the notation [q ⋅ p].
    2. Pointing paths and fibers use [y = f x] (not used in 2.2 - 2.6).
    3. The function [happly] (HoTT: [apD10]) is called [ptw] and is
       defined for dependent functions.

    Book notation [a ⥲ b] (the identity type) is HoTT's [a = b], and
    [refl a] is [idpath a].  Where the book uses judgmental equality
    [≡], we verify it by type checking [idpath] (i.e., by conversion). *)

From HoTT Require Import Basics.

Declare Scope uf_scope.
Delimit Scope uf_scope with uf.
Local Open Scope uf_scope.

(** ** 2.2 Types, elements, families, and functions *)

Section TypesElementsFamiliesFunctions.

  (** A family of types [T(x)] parametrized by [x : X] is a function
      [X -> Type]; a family of elements [e(x) : T(x)] is a dependent
      function, an element of the product type [forall x : X, T x],
      the book's [∏_{x:X} T(x)].  If [T] is constant this is the function
      type [X -> T]. *)

  (** Definition [def:cst-map]: the constant function at [t]. *)
  Definition cst {X T : Type} (t : T) : X -> T := fun _ => t.

  (** Composition of functions.  HoTT's [g o f] is [fun a => g (f a)]. *)
  Definition comp {X Y Z : Type} (g : Y -> Z) (f : X -> Y) : X -> Z
    := fun a => g (f a).

  Check (fun (X Y Z : Type) (g : Y -> Z) (f : X -> Y) =>
           idpath : comp g f = (g o f)%function).

  (** The identity function [id_X]. *)
  Definition id (X : Type) : X -> X := fun a => a.

  Context {X Y Z W : Type} (f : X -> Y) (g : Y -> Z) (h : Z -> W).

  (** Associativity holds by definition: [(h ∘ g) ∘ f ≡ h ∘ (g ∘ f)]. *)
  Definition comp_assoc_jdeq : comp (comp h g) f = comp h (comp g f)
    := idpath.

  (** Unit laws hold by definition, using the eta rule
      [f ≡ (a ↦ f(a))]. *)
  Definition comp_id_r_jdeq : comp f (id X) = f := idpath.
  Definition comp_id_l_jdeq : comp (id Y) f = f := idpath.

End TypesElementsFamiliesFunctions.

(** The examples [m ↦ (n ↦ m + n)] and [2 + _] are given in 2.4, after
    addition has been defined. *)

(** ** 2.3 Universes

    Coq-HoTT has a hierarchy of universes [Type@{i}], which is
    cumulative: if [i < j] and [X : Type@{i}] then [X : Type@{j}].
    The smallest universe [U_0] is [Type0] in Coq-HoTT, which contains
    the basic types [nat], [Empty], [Unit], ... *)

Section Universes.

  Universes i j.
  Constraint i < j.

  (** Every universe is an element of a larger one. *)
  Definition universe_in_larger : Type@{j} := Type@{i}.

  (** Cumulativity (item [it:cumulative]). *)
  Definition cumulative (X : Type@{i}) : Type@{j} := X.

  (** [U_0] contains [ℕ]. *)
  Check nat : Type0.

  (** Correspondence between families of types and functions into a
      universe: a family [T(x)] with [T(x) : U] gives [x ↦ T(x) : X -> U],
      and conversely [f' : X -> U] gives the family [f'(x)].  In Rocq
      these two views coincide: a family of types simply *is* a function
      into a universe. *)
  Definition family_to_function {X : Type@{i}} (T : X -> Type@{i})
    : X -> Type@{i} := fun x => T x.

  Definition family_to_function_eta {X : Type@{i}} (T : X -> Type@{i})
    : family_to_function T = T := idpath.

  (** Function types between types in [U] are again in [U]. *)
  Definition fun_type_in_U (X Y : Type@{i}) : Type@{i} := X -> Y.

End Universes.

(** ** 2.4 The type of natural numbers

    Rules (P1) - (P3): [nat : Type0], [O : nat], [S : nat -> nat].
    We use the natural numbers of Coq-HoTT ([Basics.Overture]), which are
    defined as an inductive type in [Type0]. *)

Module Naturals.

  Local Open Scope nat_scope.
  Local Open Scope uf_scope.

  Notation ℕ := nat.
  Notation Succ := S.

  (** Rule (P4): induction on ℕ, with its two computation rules holding
      by definition. *)
  Definition ind_N (X : ℕ -> Type) (a : X 0%nat)
    (g : forall m, X m -> X (Succ m)) : forall m, X m
    := fix f (m : ℕ) : X m :=
         match m with
         | O => a
         | S m' => g m' (f m')
         end.

  Definition ind_N_0 X a g : ind_N X a g 0%nat = a := idpath.
  Definition ind_N_S X a g m
    : ind_N X a g (Succ m) = g m (ind_N X a g m) := idpath.

  (** The recursion principle is the special case of a constant family. *)
  Definition rec_N (Y : Type) (a : Y) (g : ℕ -> Y -> Y) : ℕ -> Y
    := ind_N (fun _ => Y) a g.

  (** Iteration: [e^0 :≡ id_Y] and [e^(S m) :≡ e ∘ e^m]. *)
  Definition iter {Y : Type} (e : Y -> Y) : ℕ -> (Y -> Y)
    := rec_N (Y -> Y) (id Y) (fun _ d => comp e d).

  (** Addition, by induction on the second argument:
      [n + 0 :≡ n] and [n + S(m) :≡ S(n + m)]. *)
  Definition add (n : ℕ) : ℕ -> ℕ
    := rec_N ℕ n (fun _ k => Succ k).

  (** Multiplication, by induction on the first argument:
      [0 · n :≡ 0] and [S(m) · n :≡ (m · n) + n]. *)
  Definition mul (m n : ℕ) : ℕ
    := rec_N ℕ 0%nat (fun _ k => add k n) m.

  Local Notation "n + m" := (add n m) : uf_scope.
  Local Notation "m * n" := (mul m n) : uf_scope.

  Definition two_plus_two : 2 + 2 = 4 := idpath.

  (** Examples from 2.2: [m ↦ (n ↦ m + n)] and [2 + _]. *)
  Check (fun m => (fun n => m + n)) : ℕ -> (ℕ -> ℕ).
  Check (fun n => 2 + n) : ℕ -> ℕ.

  (** Alternative definitions via iteration:
      [n + m :≡ Succ^m(n)] and [m · n :≡ (i ↦ i + n)^m(0)].
      They are not equal by definition to [add] and [mul] for variables
      [n] and [m], but they can be identified (by induction on [m]). *)
  Definition add' (n m : ℕ) : ℕ := iter Succ m n.
  Definition mul' (m n : ℕ) : ℕ := iter (fun i => i + n) m 0%nat.

  Definition add_add' (n m : ℕ) : n + m = add' n m.
  Proof.
    induction m as [|m IH].
    - exact idpath.
    - exact (ap Succ IH).
  Defined.

  Definition mul_mul' (m n : ℕ) : m * n = mul' m n.
  Proof.
    induction m as [|m IH].
    - exact idpath.
    - exact (ap (fun i => i + n) IH).
  Defined.

  (** The factorial function:
      [fact(0) :≡ 1] and [fact(S(m)) :≡ S(m) · fact(m)]. *)
  Definition fact : ℕ -> ℕ
    := rec_N ℕ 1%nat (fun m k => Succ m * k).

  Definition fact_3 : fact 3 = 6 := idpath.

End Naturals.

(** ** 2.5 Identity types

    Rules (E1) - (E3).  (E1) is the identity type [a = b] (HoTT's
    [paths], which lives in the same universe as [X]); (E2) is
    [idpath a : a = a]; (E3) is based path induction, HoTT's
    [paths_ind], with its computation rule holding by definition.
    Possible further parameters of [P] can be absorbed into [P]. *)

Section IdentityTypes.

  Definition path_ind {X : Type} (a : X) (P : forall b : X, a = b -> Type)
    (p : P a idpath) : forall (b : X) (e : a = b), P b e
    := fun b e => match e with idpath => p end.

  Definition path_ind_refl {X : Type} (a : X) P p
    : path_ind a P p a idpath = p := idpath.

  Definition path_ind_is_paths_ind {X : Type} (a : X) P p b e
    : path_ind a P p b e = paths_ind a P p b e := idpath.

End IdentityTypes.

(** Example: [refl_2 : fact(2) = 2]. *)
Definition fact_2 : Naturals.fact 2%nat = 2%nat := idpath 2%nat.

(** Definition [def:eq-symm]: path inverse, [symm_{a,a}(refl a) :≡ refl a]. *)
Definition symm {X : Type} {a b : X} (p : a = b) : b = a
  := match p with idpath => idpath end.

Notation "p ⁻¹" := (symm p) : uf_scope.

(** Definition [def:eq-trans]: path composition, defined by induction on
    the second argument: [trans_{a,b,b}(p)(refl b) :≡ p].  This differs
    from HoTT's [concat], which is defined by induction on both
    arguments. *)
Definition trans {X : Type} {a b c : X} (p : a = b) (q : b = c) : a = c
  := match q with idpath => p end.

(** Notation in the order of function composition: [q ⋅ p :≡ p ∙ q]. *)
Notation "q ⋅ p" := (trans p q) : uf_scope.

(** Comparison with the library. *)
Definition symm_is_inverse {X : Type} {a b : X} (p : a = b)
  : p⁻¹ = p^ := match p with idpath => idpath end.

Definition trans_is_concat {X : Type} {a b c : X} (p : a = b) (q : b = c)
  : q ⋅ p = p @ q.
Proof. destruct q, p. exact idpath. Defined.

(** Exercise [xca:path-groupoid-laws]. *)
Section PathGroupoidLaws.

  Context {X : Type} {a b c d : X}.

  (** 1. [p ∙ refl_b = p] (holds by definition). *)
  Definition trans_p1 (p : a = b) : idpath ⋅ p = p := idpath.

  (** 2. [refl_a ∙ p = p]. *)
  Definition trans_1p (p : a = b) : p ⋅ idpath = p
    := match p with idpath => idpath end.

  (** 3. [(p ∙ q) ∙ r = p ∙ (q ∙ r)]. *)
  Definition trans_assoc (p : a = b) (q : b = c) (r : c = d)
    : r ⋅ (q ⋅ p) = (r ⋅ q) ⋅ p
    := match r with idpath => idpath end.

  (** 4. [p⁻¹ ∙ p = refl_b]. *)
  Definition trans_Vp (p : a = b) : p ⋅ p⁻¹ = idpath
    := match p with idpath => idpath end.

  (** 5. [p ∙ p⁻¹ = refl_a]. *)
  Definition trans_pV (p : a = b) : p⁻¹ ⋅ p = idpath
    := match p with idpath => idpath end.

  (** 6. [(p⁻¹)⁻¹ = p]. *)
  Definition symm_symm (p : a = b) : (p⁻¹)⁻¹ = p
    := match p with idpath => idpath end.

End PathGroupoidLaws.

(** Powers of a symmetry [p : a = a]: [p^0 :≡ refl_a] and
    [p^(n+1) :≡ p · p^n]; negative powers [p^(-n) :≡ (p⁻¹)^n]. *)
Fixpoint path_pow {X : Type} {a : X} (p : a = a) (n : nat) : a = a
  := match n with
     | O => idpath
     | S n' => p ⋅ path_pow p n'
     end.

Notation "p ^^ n" := (path_pow p n) (at level 30) : uf_scope.

Definition path_pow_neg {X : Type} {a : X} (p : a = a) (n : nat) : a = a
  := (p⁻¹) ^^ n.

(** Definition [def:transport]: [trp^T_{refl a} :≡ id_{T(a)}]. *)
Definition trp {X : Type} (T : X -> Type) {a b : X} (e : a = b)
  : T a -> T b
  := match e with idpath => id (T a) end.

Arguments trp {X} T {a b} e _.

Definition trp_is_transport {X : Type} (T : X -> Type) {a b : X}
  (e : a = b) (t : T a) : trp T e t = transport T e t
  := match e with idpath => idpath end.

(** Exercise [xca:trp-compose]: [trp_{e' ∘ e} = trp_{e'} ∘ trp_e].
    This is an identification of functions; no function extensionality
    is needed, since after induction on [e'] both sides are [trp_e]
    by definition. *)
Definition trp_compose {X : Type} (T : X -> Type) {a b c : X}
  (e : a = b) (e' : b = c)
  : trp T (e' ⋅ e) = comp (trp T e') (trp T e)
  := match e' with idpath => idpath end.

(** Exercise [xca:trp-nondep]: in a constant family [trp^Y_p = id_Y]. *)
Definition trp_const {X Y : Type} {a b : X} (p : a = b)
  : trp (fun _ => Y) p = id Y
  := match p with idpath => idpath end.

(** Example: transport of structure in [T(x) :≡ (x = x)], which transports
    a symmetry of [a] to a symmetry of [b]. *)
Definition trp_symmetry {X : Type} {a b : X} (e : a = b)
  : (a = a) -> (b = b)
  := trp (fun x => x = x) e.

(** By induction, this is conjugation: [trp_e(s) = e · s · e⁻¹]. *)
Definition trp_symmetry_conj {X : Type} {a b : X} (e : a = b) (s : a = a)
  : trp_symmetry e s = (e ⋅ s) ⋅ e⁻¹
  := match e with idpath => (trans_1p s)^ end.

(** ** 2.6 Product types

    If [X : U] and [Y : X -> U] then [forall x, Y x : U]. *)

Definition pi_in_U@{u} (X : Type@{u}) (Y : X -> Type@{u}) : Type@{u}
  := forall x : X, Y x.

(** Definition [def:ap]: [ap_{f,x,x}(refl x) :≡ refl_{f(x)}]. *)
Definition ap' {X Y : Type} (f : X -> Y) {x x' : X} (p : x = x')
  : f x = f x'
  := match p with idpath => idpath end.

Definition ap'_is_ap {X Y : Type} (f : X -> Y) {x x' : X} (p : x = x')
  : ap' f p = ap f p := idpath.

(** Construction [lem:apcomp]. *)
Section ApComp.

  Context {X Y : Type} (f : X -> Y) {x x' x'' : X}.

  Definition ap_trans (p : x = x') (p' : x' = x'')
    : ap' f (p' ⋅ p) = ap' f p' ⋅ ap' f p.
  Proof. destruct p', p. exact idpath. Defined.

  Definition ap_symm (p : x = x') : ap' f (p⁻¹) = (ap' f p)⁻¹
    := match p with idpath => idpath end.

  Definition ap_id (p : x = x') : ap' (id X) p = p
    := match p with idpath => idpath end.

End ApComp.

(** Exercise [xca:trp-ap]: [trp^{T ∘ f}_p = trp^T_{ap_f(p)}], both of type
    [T(f(a)) -> T(f(a'))]. *)
Definition trp_ap {X A : Type} (T : X -> Type) (f : A -> X)
  {a a' : A} (p : a = a')
  : trp (comp T f) p = trp T (ap' f p)
  := match p with idpath => idpath end.

(** Definition [def:ptw]: from an identification of (dependent) functions
    to pointwise identifications, [ptw_{f,f}(refl f) :≡ x ↦ refl_{f(x)}].
    It corresponds to HoTT's [apD10] (Book HoTT's [happly]); the two are
    not equal by definition but are identified below. *)
Definition ptw {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) : forall x : X, f x = g x
  := match p with idpath => fun x => idpath end.

Definition ptw_is_apD10 {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) : ptw p = apD10 p
  := match p with idpath => idpath end.

(** Footnote to [def:ptw]: the alternative via evaluation
    [ev_x(f) :≡ f(x)].  Not equal by definition, but identified. *)
Definition ev {X : Type} {Y : X -> Type} (x : X) : (forall x, Y x) -> Y x
  := fun f => f x.

Definition ptw_ev {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) (x : X) : ptw p x = ap' (ev x) p
  := match p with idpath => idpath end.

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
  : h x' ⋅ ap' f p = ap' g p ⋅ h x
  := match p with idpath => trans_1p (h x) end.
