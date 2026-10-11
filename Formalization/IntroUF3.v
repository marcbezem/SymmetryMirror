(** * Formalization of Sections 2.13 - 2.15 of [intro-uf.tex]

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

From HoTT Require Import Basics Types.Sigma Types.Equiv Types.Bool
  Types.Universe Types.Forall.
From SymmetryMirror Require Import IntroUF IntroUF2.

Local Open Scope uf_scope.

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

