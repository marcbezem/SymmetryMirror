(** * Formalization of Sections 3.1 - 3.3 of [circle.tex]

    Chapter 3, "The universal symmetry: the circle", of the book
    "Symmetry", in Rocq with the Coq-HoTT library.

    ** Summary of this formalization

    Sections 3.1 - 3.3 are formalized in this file, which builds on
    [IntroUF.v] (Chapter 2).  It compiles with
    [coqc -noinit -indices-matter], with nothing admitted.
    [Print Assumptions]: the higher inductive types [S1] and [ℤ] come
    from the library's graph quotients ([gqglue] and its computation
    rule); [Funext] and [Univalence] are used only where needed, and the
    results on the integers use no other axioms.

    Book notions defined from Coq-HoTT notions: the circle [S1 :≡ Circle]
    with [base] and [loop] (same names), induction [S1_ind :≡ Circle_ind]
    (its loop case is a [PathOver], i.e. the library's [DPath]) and
    recursion [S1_rec :≡ Circle_rec], both computing on [base] by
    definition.  The integers [ℤ] are the book's higher inductive type,
    realized as the library's [Pushout] of [-0 : ℕ⁻] and [0 : ℕ] over [𝟙],
    with [ι₊ :≡ pushr], [ι₋ :≡ pushl], [zeq :≡ pglue(triv)]; the
    induction principle computes on [ι₊] and [ι₋] by definition, with
    the computation rule [ℤ_ind_zeq] for [zeq].  Own definitions: [ev],
    [ve], [ev^a] ([evp]), the operations on [ℤ], coverings and their
    variants, [SetBundle], universal coverings, [R] and [exp].

    3.1 The circle and its universal property
    - [def:circle], with the computation rules.
    - [lem:freeloopspace], following the book's proof: the general
      result [S1_fun_path] (from [p : f(base) = g(base)] and
      [q : f(loop) = p⁻¹ · g(loop) · p] to [f = g]) by circle induction,
      using [lem:trp-in-fx=Ygx].
    - [cor:circle-loopspace], by the direct proof of the footnote
      (inverse [l ↦ (ve(a,l), refl_a)]).
    - Remark [rem:dep-univ-prop-circle]: the dependent universal property.
    - [lem:circleisconnected].

    3.2 The integers
    - [def:zet]; [ℤ] is a set with decidable equality, via an
      equivalence [ℤ ≃ Int] with the library's inductive integers.  Since
      [ℤ] is a set, families of identifications in a set need no [zeq]
      case ([ℤ_ind_prop]).
    - Negation (an involution, with [ap_-(zeq) :≡ zeq⁻¹]), the successor
      [zs] (with [ap_s(zeq) :≡ refl_1]) and the predecessor, so that [zs]
      is an equivalence; the iteration [f^z] of any equivalence
      [f : X ≃ X] for [z : ℤ]; addition [z + y :≡ zs^y(z)], subtraction,
      the fact that they are mutually inverse, and multiplication
      [zy :≡ (w ↦ z + w)^y(0)].
    - Exercises [xca:addition-on-Z-and-N] and [xca:commutative-add-Z].
      These, and the inverse of [w ↦ z + w], are proved by comparing the
      operations with those of the library's [Int] ([toInt_zadd],
      [toInt_zmul]) and reusing its lemmas.
    - The order [z ≤ y :≡ ∑_n (y = z + ι₊(n))], which extends [≤] on [ℕ].

    3.3 Coverings
    - [def:covering]: coverings, connected, finite and decidable
      coverings, pointed coverings, and [SetBundle(B)].
    - The equivalence [SetBundle(B) ≃ (B → Set)] of
      [lem:Prop-Set-pointed-families], in the direction of [preim] so
      that it computes by definition ([coverPreim_Eqv]), and
      [lem:setbundle-is-groupoid].
    - Exercise [xca:covering-utils], all six parts.  For part 4 we do not
      follow the hint: [f⁻¹(b)] is the fiber over [(b, refl)] of a map
      between the sets [(gf)⁻¹(g(b))] and [g⁻¹(g(b))].
    - Exercise [xca:twoS1coverings], both parts.
    - [thm:coveringsofS1perms]: [SetBundle(S1) ≃ (S1 → Set) ≃
      ∑_{X:Set}(X ≃ X)], together with [g : (S1 → U) ≃ ∑_{X:U}(X ≃ X)];
      the squares with the forgetful maps commute (the left one by
      definition, the right one by [ap_compose]).
    - Example [def:universalcover], [def:univ-cover], and
      [lem:univ-cover-of-groupoid] in both directions, with the book's
      argument for "universal implies contractible" (using associativity
      of pointed composition, [pcomp_assoc]).  The other direction does
      not need that [B] is a groupoid: pointed maps out of a contractible
      pointed type form a contractible type.
    - [def:RtoS1]: [R : S1 → U] with [R(base) :≡ ℤ], [R(loop) := etop(zs)],
      which is set-valued, and the exponential covering [exp].

    Left out
    - The alternative form of [ℤ]-induction (giving [f(0)], [g'] and [h']),
      a remark without a precise statement.
    - The remark that [∏_{z:S1}(base = z)] contradicts univalence (this
      needs [loop ≠ refl], from Section 3.4).
    - Remark [rem:subtype-diagram]: its content is used in
      [thm:coveringsofS1perms] for the particular diagrams there.

    ** Conventions

    As in [IntroUF.v]: path composition [q ⋅ p :≡ trans p q] in the order
    of function composition, fibers and pointing paths with [y = f(x)],
    and notions that occur definitionally in Coq-HoTT defined from the
    library notion and used under the book's name.  Numerals in patterns
    are written [O] since [0] in patterns refers to [trunc_index]. *)

From HoTT Require Import Basics Types.Sigma Types.Equiv Types.Universe
  Types.Forall Types.Paths Types.Bool Truncations.Core Colimits.Coeq
  Colimits.Pushout Spaces.Int Spaces.Circle.
From SymmetryMirror Require Import IntroUF.

Local Open Scope uf_scope.

(** ** 3.1 The circle and its universal property *)

(** Definition [def:circle]: the circle is the library's [Circle], with
    the constructors [base] and [loop] (same names as in the book).  The
    induction principle is the library's [Circle_ind]: its loop case is
    a path over [loop] (the book's [PathOver] is the library's [DPath],
    i.e. [trp_loop(a) = a]), and it computes on [base] by definition. *)
Definition S1 : Type := Circle.

Definition S1_ind (A : S1 -> Type) (a : A base) (l : PathOver A loop a a)
  : forall x : S1, A x
  := Circle_ind A a l.

Definition S1_ind_base (A : S1 -> Type) (a : A base) (l : PathOver A loop a a)
  : S1_ind A a l base = a := refl.

Definition S1_ind_loop (A : S1 -> Type) (a : A base) (l : PathOver A loop a a)
  : apd (S1_ind A a l) loop = l
  := Circle_ind_beta_loop A a l.

Definition S1_rec (A : Type) (a : A) (l : a = a) : S1 -> A := Circle_rec A a l.

Definition S1_rec_base (A : Type) (a : A) (l : a = a) : S1_rec A a l base = a
  := refl.

Definition S1_rec_loop (A : Type) (a : A) (l : a = a)
  : ap (S1_rec A a l) loop = l
  := Circle_rec_beta_loop A a l.

(** A family of propositions over [S1] is given by its value at [base]. *)
Definition S1_ind_prop (A : S1 -> Type) (hA : forall x, isProp (A x)) (a : A base)
  : forall x : S1, A x
  := S1_ind A a (hA base _ _).

(** Theorem [lem:freeloopspace]. *)
Section FreeLoopSpace.

  Context {A : Type}.

  Definition ev (g : S1 -> A) : {a : A & a = a} := (g base; ap g loop).

  Definition ve (w : {a : A & a = a}) : S1 -> A := S1_rec A (fst w) (snd w).

  (** The more general result in the proof: for [p : f(base) = g(base)]
      and [q : f(loop) = p⁻¹ · g(loop) · p] we get [f = g]. *)
  Definition conj_cancel {x y : A} (p : x = y) (s : x = y)
    : (s ⋅ (p⁻¹ ⋅ s)⁻¹) = p.
  Proof. destruct p. exact (trans_Vp s). Defined.

  Definition S1_htpy {f g : S1 -> A} (p : f base = g base)
    (q : ap f loop = p⁻¹ ⋅ (ap g loop ⋅ p))
    : forall x, f x = g x.
  Proof.
    refine (S1_ind (fun x => f x = g x) p _).
    refine (trp_paths_fg f g loop p @ _).
    refine (ap (fun r => (ap g loop ⋅ p) ⋅ r⁻¹) q @ _).
    exact (conj_cancel p (ap g loop ⋅ p)).
  Defined.

  Definition S1_fun_path `{Funext} {f g : S1 -> A} (p : f base = g base)
    (q : ap f loop = p⁻¹ ⋅ (ap g loop ⋅ p))
    : f = g
    := ptw_inv (S1_htpy p q).

  Definition ev_isEquiv `{Funext} : isEquiv ev.
  Proof.
    refine (iso_to_isEquiv ev ve _ _).
    - intro f. exact (S1_fun_path (f := ve (ev f)) (g := f) refl
                        (S1_rec_loop _ _ _ @ (trans_1p _)^)).
    - intros [a l]. exact (ap (fun r => (a; r) : {a : A & a = a}) (S1_rec_loop A a l)).
  Defined.

  Definition ev_Eqv `{Funext} : (S1 -> A) ≃ {a : A & a = a} := (ev; ev_isEquiv).

End FreeLoopSpace.

Arguments ev A g : clear implicits.
Arguments ve A w : clear implicits.

(** The circle pointed at [base]. *)
Definition S1star : Ustar := (S1; base).

(** Corollary [cor:circle-loopspace].  We follow the direct proof of the
    footnote: the inverse sends [l] to [(ve(a,l), refl_a)]. *)
Section CircleLoopSpace.

  Context {A : Type}.

  Definition evp (a : A) (g : S1star →* (A; a)) : a = a
    := (snd g)⁻¹ ⋅ (ap (fst g) loop ⋅ snd g).

  Definition evp_inv (a : A) (l : a = a) : S1star →* (A; a)
    := (ve A (a; l); refl).

  Definition evp_inv_evp `{Funext} (a : A) (g : S1star →* (A; a))
    : evp_inv a (evp a g) = g.
  Proof.
    destruct g as [f p]. change (S1 -> A) in f. change (a = f base) in p.
    revert a p. refine (paths_ind_r _ _ _).
    refine (eqinv (snd (ptw_star _ _)) _).
    exact (S1_htpy (f := ve A (f base; evp (f base) (f; refl))) (g := f) refl
             (S1_rec_loop _ _ _); refl).
  Defined.

  Definition evp_isEquiv `{Funext} (a : A) : isEquiv (evp a)
    := iso_to_isEquiv (evp a) (evp_inv a) (evp_inv_evp a)
         (fun l => trans_1p _ @ S1_rec_loop A a l).

End CircleLoopSpace.

(** Remark [rem:dep-univ-prop-circle]: the dependent universal property. *)
Section DepUnivProp.

  Context {A : S1 -> Type}.

  Definition evd (g : forall x, A x) : {a : A base & PathOver A loop a a}
    := exist (fun a : A base => PathOver A loop a a) (g base) (apd g loop).

  Definition evd_isEquiv `{Funext} : isEquiv evd.
  Proof.
    refine (iso_to_isEquiv evd (fun w => S1_ind A (fst w) (snd w)) _ _).
    - intro g. apply ptw_inv.
      refine (S1_ind _ refl _).
      refine (trp_paths_dep _ g loop refl @ _). cbn.
      refine (ap (fun r => (po_to_trp (apd g loop) ⋅ refl) ⋅ (po_to_trp r)⁻¹)
                 (S1_ind_loop _ _ _) @ _).
      exact (ap (fun r => r ⋅ (po_to_trp (apd g loop))⁻¹) (trans_1p _) @ trans_Vp _).
    - intros [a l]. exact (ap (fun r => (a; r) : {a : A base & PathOver A loop a a})
                              (S1_ind_loop A a l)).
  Defined.

End DepUnivProp.

(** Lemma [lem:circleisconnected]. *)
Definition S1_base_paths : forall z : S1, ptrunc (base = z)
  := S1_ind_prop (fun z => ptrunc (base = z)) (fun _ => ptrunc_isProp) (trunc refl).

Definition S1_isConn : isConn S1
  := (trunc base;
      fun x y => ptrunc_rec ptrunc_isProp
                   (fun p => ptrunc_rec ptrunc_isProp (fun q => trunc (q ⋅ p⁻¹))
                               (S1_base_paths y))
                   (S1_base_paths x)).

(** ** 3.2 The integers *)

(** Definition [def:zet]: the higher inductive type [ℤ] with constructors
    [ι₊ : ℕ → ℤ], [ι₋ : ℕ⁻ → ℤ] and [zeq : ι₋(-0) = ι₊(0)] is the
    pushout of [-0 : ℕ⁻] and [0 : ℕ] over [𝟙], the library's [Pushout].
    Its induction principle computes on [ι₊] and [ι₋] by definition. *)
Definition ℤ : Type := Pushout (fun _ : True => negN 0%nat) (fun _ : True => 0%nat).

Definition iplus (n : ℕ) : ℤ := pushr n.
Definition iminus (m : NNN) : ℤ := pushl m.
Definition zeq : iminus (negN 0) = iplus 0 := pglue tt.

Definition ℤ_ind (T : ℤ -> Type) (g : forall n, T (iplus n))
  (h : forall m, T (iminus m)) (q : PathOver T zeq (h (negN 0)) (g 0%nat))
  : forall z, T z
  := Pushout_ind T h g (fun t => match t with tt => q end).

Definition ℤ_ind_plus T g h q n : ℤ_ind T g h q (iplus n) = g n := refl.
Definition ℤ_ind_minus T g h q m : ℤ_ind T g h q (iminus m) = h m := refl.
Definition ℤ_ind_zeq T g h q : apd (ℤ_ind T g h q) zeq = q
  := Pushout_ind_beta_pglue T h g _ tt.

Definition ℤ_rec (T : Type) (g : ℕ -> T) (h : NNN -> T) (q : h (negN 0) = g 0%nat)
  : ℤ -> T
  := Pushout_rec T h g (fun _ => q).

Definition ℤ_rec_zeq T g h q : ap (ℤ_rec T g h q) zeq = q
  := Pushout_rec_beta_pglue T h g _ tt.

(** [ℤ] is a set with decidable equality: it is equivalent to the
    library's inductive type [Int]. *)
Definition toInt : ℤ -> Int
  := ℤ_rec Int int_of_nat (fun m => int_neg (int_of_nat (unneg m))) refl.

Definition fromInt (x : Int) : ℤ
  := match x with
     | negS n => iminus (negN (S n))
     | zero => iplus 0
     | posS n => iplus (S n)
     end.

Definition toInt_fromInt (x : Int) : toInt (fromInt x) = x
  := match x with negS _ | zero | posS _ => refl end.

Definition fromInt_toInt (z : ℤ) : fromInt (toInt z) = z.
Proof.
  pose (g := fun n : ℕ => match n as n' return fromInt (toInt (iplus n')) = iplus n' with
                      | O => refl | S _ => refl end).
  pose (h := fun m : NNN => match m as m' return fromInt (toInt (iminus m')) = iminus m' with
                      | negN n =>
                          match n as n' return fromInt (toInt (iminus (negN n')))
                                               = iminus (negN n') with
                          | O => zeq⁻¹ | S _ => refl end
                      end).
  refine (ℤ_ind (fun z => fromInt (toInt z) = z) g h _ z).
  - refine (trp_paths_fg (fun z => fromInt (toInt z)) idmap zeq zeq⁻¹ @ _).
    refine (ap (fun r => (ap idmap zeq ⋅ zeq⁻¹) ⋅ r⁻¹)
              (ap_compose toInt fromInt zeq @ ap (ap fromInt) (ℤ_rec_zeq _ _ _ _)) @ _).
    refine (trans_1p _ @ _).
    exact (ap (fun r => r ⋅ zeq⁻¹) (ap_idmap zeq) @ trans_Vp zeq).
Defined.

Definition ℤ_Int : ℤ ≃ Int := mkEqv toInt fromInt fromInt_toInt toInt_fromInt.

Definition Int_isSet : isSet Int := IsHSet_isSet ishset_int.

Definition ℤ_isSet : isSet ℤ := is_ntype_Eqv 0 (Eqv_inv ℤ_Int) Int_isSet.

Definition toInt_inj {x y : ℤ} (e : toInt x = toInt y) : x = y
  := (fromInt_toInt x)^ @ ap fromInt e @ fromInt_toInt y.

Definition ℤ_isDecSet : isDecSet ℤ
  := hedberg (fun x y => match dec_paths (toInt x) (toInt y) with
                         | inl e => inl (toInt_inj e)
                         | inr n => inr (fun e => n (ap toInt e))
                         end).

(** Since [ℤ] is a set, families of identifications in [ℤ] (or in any
    set) need no loop case. *)
Definition ℤ_ind_prop (T : ℤ -> Type) (hT : forall z, isProp (T z))
  (g : forall n, T (iplus n)) (h : forall m, T (iminus m)) : forall z, T z
  := ℤ_ind T g h (hT _ _ _).

(** Negation, with [ap_-(zeq) :≡ zeq⁻¹]; it is its own inverse. *)
Definition zneg : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => iminus (negN n)) (fun m => iplus (unneg m)) zeq⁻¹.

Definition zneg_zneg (z : ℤ) : zneg (zneg z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intro n. exact refl.
  - intros [n]. exact refl.
Defined.

Definition znegEqv : ℤ ≃ ℤ := mkEqv zneg zneg zneg_zneg zneg_zneg.

(** The successor [zs], with [ap_s(zeq) :≡ refl_1], and the predecessor
    [zp], its inverse. *)
Definition zs : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => iplus (S n))
       (fun m => match m with
                 | negN O => iplus 1
                 | negN (S n) => iminus (negN n)
                 end)
       refl.

Definition zp : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => match n with O => iminus (negN 1) | S n => iplus n end)
       (fun m => iminus (negN (S (unneg m))))
       refl.

Definition zp_zs (z : ℤ) : zp (zs z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intro n. exact refl.
  - intros [[|n]]; [exact zeq⁻¹ | exact refl].
Defined.

Definition zs_zp (z : ℤ) : zs (zp z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intros [|n]; [exact zeq | exact refl].
  - intros [n]. exact refl.
Defined.

Definition zsEqv : ℤ ≃ ℤ := mkEqv zs zp zp_zs zs_zp.

(** The inverse of an equivalence built by [mkEqv] is the given one. *)
Definition eqinv_mkEqv {X Y : Type} (f : X -> Y) (g : Y -> X) gf fg (y : Y)
  : eqinv (snd (mkEqv f g gf fg)) y = g y
  := ap (eqinv (snd (mkEqv f g gf fg))) (fg y)^ @ eqinv_l _ (g y).

(** Iteration [f^z] of an equivalence [f : X ≃ X], for [z : ℤ]:
    [f^{ι₊(n)} :≡ f^n], [f^{ι₋(-n)} :≡ (f⁻¹)^n], and [f^0 ≡ id ≡ f^{-0}]. *)
Definition iterZ {X : Type} (f : X ≃ X) : ℤ -> X -> X
  := ℤ_rec (X -> X) (fun n => iter (fst f) n)
       (fun m => iter (eqinv (snd f)) (unneg m)) refl.

(** Addition [z + y :≡ zs^y(z)], subtraction [z - y :≡ z + (-y)]. *)
Definition zadd (z y : ℤ) : ℤ := iterZ zsEqv y z.
Definition zsub (z y : ℤ) : ℤ := zadd z (zneg y).

(** Comparison of the operations with those of the library's [Int]. *)
Definition toInt_zs (x : ℤ) : toInt (zs x) = int_succ (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intros [|n]; exact refl.
  - intros [[|[|n]]]; exact refl.
Defined.

Definition toInt_zp (x : ℤ) : toInt (zp x) = int_pred (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intros [|[|n]]; exact refl.
  - intros [[|n]]; exact refl.
Defined.

Definition toInt_zneg (x : ℤ) : toInt (zneg x) = int_neg (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intro n. exact refl.
  - intros [[|n]]; exact refl.
Defined.

Definition int_pred_neg (n : ℕ)
  : int_pred (int_neg (int_of_nat n)) = int_neg (int_of_nat (S n))
  := match n with O => refl | S _ => refl end.

Definition toInt_zadd (z y : ℤ) : toInt (zadd z y) = int_add (toInt z) (toInt y).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ y).
  - intro n. change (toInt (iter zs n z) = int_add (toInt z) (int_of_nat n)).
    induction n as [|n IH].
    + exact (int_add_0_r _)^.
    + exact (toInt_zs _ @ ap int_succ IH @ (int_add_succ_r _ _)^
             @ ap (int_add (toInt z)) (int_nat_succ n)).
  - intros [n].
    change (toInt (iter (eqinv (snd zsEqv)) n z)
            = int_add (toInt z) (int_neg (int_of_nat n))).
    induction n as [|n IH].
    + exact (int_add_0_r _)^.
    + exact (ap toInt (eqinv_mkEqv zs zp zp_zs zs_zp _) @ toInt_zp _
             @ ap int_pred IH @ (int_add_pred_r _ _)^
             @ ap (int_add (toInt z)) (int_pred_neg n)).
Defined.

(** Exercise [xca:addition-on-Z-and-N], for addition. *)
Definition iplus_add (n m : ℕ) : iplus (add n m) = zadd (iplus n) (iplus m)
  := toInt_inj (x := iplus (add n m)) ((int_nat_add m n)^ @ int_add_comm _ _ @ (toInt_zadd (iplus n) (iplus m))^).

(** Addition and subtraction are mutually inverse. *)
Definition zsub_zadd (w z : ℤ) : zsub (zadd w z) z = w.
Proof.
  apply toInt_inj. unfold zsub.
  refine (toInt_zadd _ _ @ ap011 int_add (toInt_zadd _ _) (toInt_zneg _) @ _).
  exact ((int_add_assoc _ _ _)^ @ ap (int_add (toInt w)) (int_add_neg_r _)
         @ int_add_0_r _).
Defined.

Definition zadd_zsub (w z : ℤ) : zadd (zsub w z) z = w.
Proof.
  apply toInt_inj. unfold zsub.
  refine (toInt_zadd _ _ @ ap (fun t => int_add t (toInt z))
            (toInt_zadd _ _ @ ap (int_add (toInt w)) (toInt_zneg _)) @ _).
  exact ((int_add_assoc _ _ _)^ @ ap (int_add (toInt w)) (int_add_neg_l _)
         @ int_add_0_r _).
Defined.

(** Hence [w ↦ z + w] is an equivalence, which we iterate to define
    multiplication [zy :≡ (w ↦ z + w)^y(0)]. *)
Definition zaddEqv (z : ℤ) : ℤ ≃ ℤ.
Proof.
  refine (mkEqv (zadd z) (fun w => fromInt (int_add (int_neg (toInt z)) (toInt w))) _ _).
  - intro w. refine (_ @ fromInt_toInt w). apply ap.
    exact (ap (int_add _) (toInt_zadd z w) @ int_add_assoc _ _ _
           @ ap (fun t => int_add t (toInt w)) (int_add_neg_l _)).
  - intro w. apply toInt_inj.
    exact (toInt_zadd _ _ @ ap (int_add (toInt z)) (toInt_fromInt _)
           @ int_add_assoc _ _ _
           @ ap (fun t => int_add t (toInt w)) (int_add_neg_r _)).
Defined.

Definition zmul (z y : ℤ) : ℤ := iterZ (zaddEqv z) y (iplus 0).

Definition toInt_zmul (z y : ℤ) : toInt (zmul z y) = int_mul (toInt z) (toInt y).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ y).
  - intro n. change (toInt (iter (zadd z) n (iplus 0)) = int_mul (toInt z) (int_of_nat n)).
    induction n as [|n IH].
    + exact (int_mul_0_r _)^.
    + exact (toInt_zadd _ _ @ ap (int_add (toInt z)) IH @ (int_mul_succ_r _ _)^
             @ ap (int_mul (toInt z)) (int_nat_succ n)).
  - intros [n].
    change (toInt (iter (eqinv (snd (zaddEqv z))) n (iplus 0))
            = int_mul (toInt z) (int_neg (int_of_nat n))).
    induction n as [|n IH].
    + exact (int_mul_0_r _)^.
    + exact (ap toInt (eqinv_mkEqv (zadd z)
                         (fun w => fromInt (int_add (int_neg (toInt z)) (toInt w))) _ _ _)
             @ toInt_fromInt _
             @ ap (int_add (int_neg (toInt z))) IH @ (int_mul_pred_r _ _)^
             @ ap (int_mul (toInt z)) (int_pred_neg n)).
Defined.

(** Exercise [xca:addition-on-Z-and-N], for multiplication. *)
Definition iplus_mul (n m : ℕ) : iplus (mul n m) = zmul (iplus n) (iplus m)
  := toInt_inj (x := iplus (mul n m)) ((int_nat_mul n m)^ @ (toInt_zmul (iplus n) (iplus m))^).

(** Exercise [xca:commutative-add-Z]. *)
Definition zadd_comm (x y : ℤ) : zadd x y = zadd y x
  := toInt_inj (toInt_zadd x y @ int_add_comm _ _ @ (toInt_zadd y x)^).

Definition zmul_comm (x y : ℤ) : zmul x y = zmul y x
  := toInt_inj (toInt_zmul x y @ int_mul_comm _ _ @ (toInt_zmul y x)^).

(** The order [z ≤ y :≡ ∑_{n:ℕ} (y = z + ι₊(n))] extends the order on [ℕ]. *)
Definition zle (z y : ℤ) : Type := {n : ℕ & y = zadd z (iplus n)}.

Definition nat_of_int (x : Int) : ℕ
  := match x with posS n => S n | _ => 0%nat end.

Definition iplus_inj {n m : ℕ} (e : iplus n = iplus m) : n = m.
Proof.
  pose (c := fun k : ℕ => match k as k' return nat_of_int (toInt (iplus k')) = k' with
                          | O => refl | S _ => refl end).
  exact ((c n)^ @ ap (fun z => nat_of_int (toInt z)) e @ c m).
Defined.

Definition le_zle (m n : ℕ)
  : (le m n -> zle (iplus m) (iplus n)) × (zle (iplus m) (iplus n) -> le m n).
Proof.
  refine (_; _).
  - intros [k e]. exact (k; ap iplus (e^ @ add_comm k m) @ iplus_add m k).
  - intros [k e]. exact (k; add_comm k m @ iplus_inj (iplus_add m k @ e^)).
Defined.

(** ** 3.3 Coverings *)

(** Definition [def:covering]. *)
Definition isCovering {A B : Type} (f : A -> B) : Type
  := forall b : B, isSet (fiber f b).

Definition isConnCovering {A B : Type} (f : A -> B) : Type
  := isCovering f × isConn A.

Definition isFinCovering {A B : Type} (f : A -> B) : Type
  := forall b : B, isFinSet (fiber f b).

Definition isDecCovering {A B : Type} (f : A -> B) : Type
  := forall b : B, isDecSet (fiber f b).

(** Pointed coverings.  By the footnote ([xca:freemaps]), a map out of a
    pointed type is the same as a pointed map to its image of the point. *)
Definition isPtdCovering {A B : Ustar} (f : A →* B) : Type := isCovering (fst f).

(** [SetBundle(B) :≡ ∑_{A:U} ∑_{f:A→B} ∏_{b:B} isSet(f⁻¹(b))]. *)
Definition SetBundle (B : Type) : Type
  := {A : Type & {f : A -> B & forall b, isSet (fiber f b)}}.

(** The equivalence with [B → Set] from [lem:Prop-Set-pointed-families],
    in the direction [f(A,h) :≡ (b ↦ h⁻¹(b))] (the restriction of
    [preim]), so that it computes by definition. *)
Section SetBundleFamilies.

  Context `{Univalence} (B : Type).

  Definition coverPreim (w : SetBundle B) : B -> SetU
    := fun b => (fiber (fst (snd w)) b; snd (snd w) b).

  Definition coverPreim_Eqv : SetBundle B ≃ (B -> SetU).
  Proof.
    refine (Eqv_comp (sigma_assoc Type (fun A => A -> B)
                        (fun A f => forall b, isSet (fiber f b))) _).
    refine (Eqv_comp (Eqv_of_Equiv (equiv_functor_sigma_pb
                        (Q := fun F : B -> Type => forall b, isSet (F b))
                        (Equiv_of_Eqv (preim_eqv B)))) _).
    exact (mkEqv (fun (w : {F : B -> Type & forall b, isSet (F b)}) (b : B) =>
                    (fst w b; snd w b) : SetU)
                 (fun S : B -> SetU =>
                    ((fun b => fst (S b)); (fun b => snd (S b)))
                    : {F : B -> Type & forall b, isSet (F b)})
                 (fun w => refl) (fun S => refl)).
  Defined.

  Definition coverPreim_Eqv_fun (w : SetBundle B)
    : fst coverPreim_Eqv w = coverPreim w := refl.

  (** Lemma [lem:setbundle-is-groupoid]. *)
  Definition SetBundle_isGrpd : isGrpd (SetBundle B)
    := is_ntype_Eqv 1 (Eqv_inv coverPreim_Eqv) (Pi_ntype 1 (fun _ => SetU_isGrpd)).

End SetBundleFamilies.

(** Exercise [xca:covering-utils]. *)
Section CoveringUtils.

  (** 1. [A → 𝟙] is a covering iff [A] is a set. *)
  Definition fiber_toTrue_eqv {A : Type} (t : True)
    : fiber (fun _ : A => tt) t ≃ A
    := mkEqv fst (fun a => (a; True_isProp t tt))
         (fun w => path_sigma_prop (fun _ => prop_is_set True_isProp _ _)
                     (u := (fst w; True_isProp t tt)) (v := w) refl)
         (fun a => refl).

  Definition covering_toTrue (A : Type)
    : (isCovering (fun _ : A => tt) -> isSet A)
      × (isSet A -> isCovering (fun _ : A => tt))
    := (fun c => is_ntype_Eqv 0 (fiber_toTrue_eqv tt) (c tt);
        fun s t => is_ntype_Eqv 0 (Eqv_inv (fiber_toTrue_eqv t)) s).

  (** 2. [x ↦ b] from [𝟙] to [B] is a covering iff [b = b] is a set. *)
  Definition fiber_fromTrue_eqv {B : Type} (b b' : B)
    : fiber (fun _ : True => b) b' ≃ (b' = b).
  Proof.
    refine (mkEqv (fun w : fiber (fun _ : True => b) b' => snd w)
                  (fun p => (tt; p)) _ (fun p => refl)).
    intros [[] p]. exact refl.
  Defined.

  Definition isSet_from_inh {X : Type} (h : X -> isSet X) : isSet X
    := fun x y => h x x y.

  Definition covering_fromTrue {B : Type} (b : B)
    : (isCovering (fun _ : True => b) -> isSet (b = b))
      × (isSet (b = b) -> isCovering (fun _ : True => b))
    := (fun c => is_ntype_Eqv 0 (fiber_fromTrue_eqv b b) (c b);
        fun s b' => is_ntype_Eqv 0 (Eqv_inv (fiber_fromTrue_eqv b b'))
                      (isSet_from_inh (fun p : b' = b =>
                                         is_ntype_Eqv 0 (eq_l_eqv p⁻¹) s))).

  (** 3. Coverings compose; the fibers of [gf] are sums of fibers. *)
  Definition fiber_comp_eqv {A B C : Type} (f : A -> B) (g : B -> C) (c : C)
    : fiber (g ∘ f) c ≃ {w : fiber g c & fiber f (fst w)}.
  Proof.
    refine (mkEqv (fun v : fiber (g ∘ f) c =>
                     ((f (fst v); snd v) : fiber g c; (fst v; refl))
                     : {w : fiber g c & fiber f (fst w)})
                  (fun u : {w : fiber g c & fiber f (fst w)} =>
                     (fst (snd u); ap g (snd (snd u)) ⋅ snd (fst u)) : fiber (g ∘ f) c)
                  _ _).
    - intros [a p]. exact refl.
    - intros [[b p] [a q]]. cbn in p, q |- *.
      revert b q p. refine (paths_ind_r _ _ _). intro p. exact refl.
  Defined.

  Definition covering_comp {A B C : Type} {f : A -> B} {g : B -> C}
    (cf : isCovering f) (cg : isCovering g) : isCovering (g ∘ f)
    := fun c => is_ntype_Eqv 0 (Eqv_inv (fiber_comp_eqv f g c))
                  (Sigma_isSet (cg c) (fun w => cf (fst w))).

  (** 4. If [g] and [gf] are coverings, then so is [f].  Instead of the
      book's hint we use that [f⁻¹(b)] is the fiber over [(b, refl)] of
      the projection [(gf)⁻¹(g(b)) ≃ ∑_{w : g⁻¹(g(b))} f⁻¹(fst w) → g⁻¹(g(b))],
      a map between sets. *)
  Definition fiber_sets_isSet {X Y : Type} (h : X -> Y) (sX : isSet X)
    (sY : isSet Y) (y : Y) : isSet (fiber h y)
    := Sigma_isSet sX (fun x => prop_is_set (sY _ _)).

  Definition covering_cancel {A B C : Type} {f : A -> B} {g : B -> C}
    (cg : isCovering g) (cgf : isCovering (g ∘ f)) : isCovering f
    := fun b => is_ntype_Eqv 0
         (Eqv_inv (fst_fiber_eqv (fun w : fiber g (g b) => fiber f (fst w)) (b; refl)))
         (fiber_sets_isSet fst (is_ntype_Eqv 0 (fiber_comp_eqv f g (g b)) (cgf (g b)))
            (cg (g b)) (b; refl)).

  (** 5. A covering of a groupoid by a connected type [A] with a
      connected loop type [a = a] has a contractible domain. *)
  Definition loops_conj {X : Type} {x y : X} (p : x = y) : (x = x) ≃ (y = y).
  Proof. destruct p. exact (idEqv _). Defined.

  Definition covering_conn_isContr `{Funext} {A B : Type} {f : A -> B} (a : A)
    (cA : isConn A) (ca : isConn (a = a)) (gB : isGrpd B) (cf : isCovering f)
    : isContr A.
  Proof.
    pose (inj := fun r => fibers_paths_Q f isProp (fun X Y e h => isProp_Eqv e h)
                            (fun b z z' => cf b z z') a a r : isProp (fiber (ap f) r)).
    pose (sa := inj_ntype 0 (f := @ap A B f a a) inj (gB (f a) (f a))).
    pose (cl := conn_set_isContr ca sa).
    apply (conn_loops_prop_isContr cA). intro x.
    exact (ptrunc_rec (isProp_isProp _)
             (fun p : a = x => isProp_Eqv (loops_conj p) (isContr_isProp' cl))
             (snd cA a x)).
  Defined.

  (** 6. A covering of an [n]-type ([n ≥ 0]) has an [n]-type as domain. *)
  Fixpoint set_ntype (n : ℕ) {X : Type} (s : isSet X) : is_ntype n X
    := match n with
       | O => s
       | S n => fun x y => set_ntype n (prop_is_set (s x y))
       end.

  Definition covering_ntype `{Funext} (n : ℕ) {A B : Type} {f : A -> B}
    (cf : isCovering f) (hB : is_ntype n B) : is_ntype n A
    := is_ntype_Eqv n (sum_of_fibers f)
         (Sigma_ntype n hB (fun b => set_ntype n (cf b))).

End CoveringUtils.

(** Exercise [xca:twoS1coverings]. *)
Section TwoS1Coverings.

  Context `{Univalence}.

  Definition BoolSet : SetU := (Bool; isSet_bool).

  Definition c_Bool : S1 -> SetU := fun _ => BoolSet.

  Definition veSet (X : SetU) (l : X = X) : S1 -> SetU := ve SetU (X; l).

  (** 1. [∑_{z:S1} 𝟚] is not connected, and [c_𝟚 = ve_Set(𝟚, refl)]. *)
  Definition const_cover_not_conn : ¬ isConn {z : S1 & Bool}
    := fun c => ptrunc_rec False_isProp (fun e : ((base; yes) : {z : S1 & Bool}) = (base; no) =>
                                 yes_ne_no (ap (fun w : {z : S1 & Bool} => snd w) e))
                  (snd c (base; yes) (base; no)).

  Definition c_Bool_refl : c_Bool = veSet BoolSet refl
    := S1_fun_path (f := c_Bool) (g := veSet BoolSet refl) refl
         (ap_const loop BoolSet @ (trans_1p _ @ S1_rec_loop SetU BoolSet refl)^).

  (** 2. With [swap] lifted to [Set], [A :≡ ∑_{z:S1} ve_Set(𝟚, swap)(z)] is
      connected, and [c_𝟚 ≠ ve_Set(𝟚, swap)]. *)
  Definition swapSet : BoolSet = BoolSet
    := path_sigma_prop (u := BoolSet) (v := BoolSet) (fun X => isSet_isProp X) swap.

  Definition ap_fst_swapSet : ap (fun X : SetU => fst X) swapSet = swap
    := ap_fst_pathpair _ _.

  Definition A2 : Type := {z : S1 & fst (veSet BoolSet swapSet z)}.

  Definition trp_A2_loop
    : trp (fun z => fst (veSet BoolSet swapSet z)) loop yes = no.
  Proof.
    refine (transport_compose (fun X : SetU => fst X) (veSet BoolSet swapSet) loop yes @ _).
    refine (ap (fun r : BoolSet = BoolSet => trp (fun X : SetU => fst X) r yes)
              (S1_rec_loop SetU BoolSet swapSet) @ _).
    refine (transport_compose (fun T : Type => T) (fun X : SetU => fst X) swapSet yes @ _).
    refine (ap (fun r => transport idmap r yes) ap_fst_swapSet @ _).
    exact (ptw (ap fst (ptoe_etop swapEqv)) yes).
  Defined.

  Definition A2_paths (w : A2) : ptrunc (((base; yes) : A2) = w).
  Proof.
    destruct w as [z x]. revert z x.
    refine (S1_ind_prop (fun z => forall x, ptrunc (((base; yes) : A2) = (z; x)))
              (fun z => Pi_isProp (fun _ => ptrunc_isProp)) _).
    intros [|].
    - exact (trunc refl).
    - exact (trunc (pathpair (Y := fun z => fst (veSet BoolSet swapSet z)) loop trp_A2_loop)).
  Defined.

  Definition A2_isConn : isConn A2
    := (trunc (base; yes);
        fun w w' => ptrunc_rec ptrunc_isProp
                      (fun p => ptrunc_rec ptrunc_isProp (fun q => trunc (q ⋅ p⁻¹))
                                  (A2_paths w'))
                      (A2_paths w)).

  Definition trp_loops_refl {X : Type} {x y : X} (p : x = y)
    : trp (fun z => z = z) p refl = refl.
  Proof. destruct p. exact refl. Defined.

  Definition c_Bool_ne_swap : ¬ (c_Bool = veSet BoolSet swapSet).
  Proof.
    intro e.
    pose (e' := (ap (fun r => (BoolSet; r) : {X : SetU & X = X}) (ap_const loop BoolSet))^
                @ ap (ev SetU) e
                @ ap (fun r => (BoolSet; r) : {X : SetU & X = X})
                     (S1_rec_loop SetU BoolSet swapSet)).
    pose (s := pathsplit (Y := fun X : SetU => X = X) e').
    pose (r := (trp_loops_refl (fst s))^ @ snd s : refl = swapSet).
    exact (refl_ne_swap (ap (ap fst) r @ ap_fst_pathpair _ _)).
  Defined.

End TwoS1Coverings.

(** Theorem [thm:coveringsofS1perms].  The second row:
    [preim : ∑_{A:U}(A → S1) ≃ (S1 → U)] and
    [g(S) :≡ (S(base), trp^{id_U}_{S(loop)})], an equivalence by
    [lem:freeloopspace] and univalence; the third row: their restrictions
    [SetBundle(S1) ≃ (S1 → Set) ≃ ∑_{X:Set}(X ≃ X)].  The vertical maps
    forget the properties; the squares commute, the left one by
    definition. *)
Section CoveringsOfS1.

  Context `{Univalence}.

  Definition gU : (S1 -> Type) ≃ {X : Type & X ≃ X}
    := Eqv_comp (ev_Eqv (A := Type))
         (tot (fun X (p : X = X) => idtoeqv p); tot_isEquiv _ (fun X => ua X X)).

  Definition gU_fun (S : S1 -> Type) : fst gU S = exist (fun X : Type => X ≃ X) (S base) (idtoeqv (ap S loop))
    := refl.

  Definition gSet : (S1 -> SetU) ≃ {X : SetU & fst X ≃ fst X}
    := Eqv_comp (ev_Eqv (A := SetU))
         (tot (fun X (p : X = X) => idtoeqv (ap fst p));
          tot_isEquiv _ (fun X => snd (Eqv_comp (subtype_paths_eqv
                                                   (fun Y => isSet_isProp Y) X X)
                                                (idtoeqv; ua _ _)))).

  Definition coverings_S1 : SetBundle S1 ≃ {X : SetU & fst X ≃ fst X}
    := Eqv_comp (coverPreim_Eqv S1) gSet.

  Definition forget_left_square (w : SetBundle S1)
    : preim S1 (fst w; fst (snd w)) = (fun z => fst (fst (coverPreim_Eqv S1) w z))
    := refl.

  Definition forget_right_square (S : S1 -> SetU)
    : fst gU (fun z => fst (S z))
      = exist (fun X : Type => X ≃ X) (fst (fst (fst gSet S))) (snd (fst gSet S))
    := ap (fun r => exist (fun X : Type => X ≃ X) (fst (S base)) (idtoeqv r))
          (ap_compose S fst loop).

End CoveringsOfS1.

(** Example [def:universalcover]: [uc_{b₀}(b) :≡ (b₀ = b)] over a
    groupoid; the alternative forms [fst] and [cst_{b₀} : 𝟙 → B]. *)
Definition uc {B : Type} (b0 : B) : B -> Type := fun b => b0 = b.

Definition uc_covering {B : Type} (gB : isGrpd B) (b0 : B)
  : isCovering (@fst B (uc b0))
  := fun b => is_ntype_Eqv 0 (fst_fiber_eqv (uc b0) b) (gB b0 b).

Definition uc_Tot_isContr {B : Type} (b0 : B) : isContr (Tot (uc b0))
  := singleton_contr b0.

Definition cst_covering {B : Type} (gB : isGrpd B) (b0 : B)
  : isCovering (fun _ : True => b0)
  := snd (covering_fromTrue b0) (gB b0 b0).

(** Definition [def:univ-cover]. *)
Definition isUnivCovering {A B : Ustar} (f : A →* B) : Type
  := forall (C : Ustar) (g : C →* B), isPtdCovering g
       -> isContr {h : A →* C & f = pcomp g h}.

(** Lemma [lem:univ-cover-of-groupoid]. *)
Section UnivCoverOfGroupoid.

  Context `{Funext}.

  Definition isContr_paths {X : Type} (c : isContr X) (x y : X) : isContr (x = y)
    := isProp_inhabited_isContr (prop_is_set (isContr_isProp' c) x y)
         (isContr_isProp' c x y).

  (** Pointed maps out of a contractible pointed type form a contractible
      type. *)
  Definition pmap_dom_isContr (A Y : Ustar) (c : isContr (utype A))
    : isContr (A →* Y).
  Proof.
    refine (isContr_Eqv (Eqv_inv (mkEqv
              (fun g : A →* Y => (fst g (pt A); snd g) : {y : utype Y & pt Y = y})
              (fun w => ((fun _ => fst w); snd w) : A →* Y) _ (fun w => refl)))
              (singleton_contr (pt Y))).
    intros [g p]. change (utype A -> utype Y) in g. change (pt Y = g (pt A)) in p.
    pose (k := fun x => isContr_isProp' c (pt A) x).
    refine (eqinv (snd (ptw_star (((fun _ => g (pt A)); p) : A →* Y) ((g; p) : A →* Y))) _).
    refine (exist _ (fun x => ap g (k x)) _).
    exact (ap (fun r => ap g r ⋅ p) (prop_is_set (isContr_isProp' c) _ _ (k (pt A)) refl)).
  Defined.

  Definition contr_univCovering {A B : Ustar} (f : A →* B) (c : isContr (utype A))
    : isUnivCovering f
    := fun C g _ => Sigma_isContr (pmap_dom_isContr A C c)
                      (fun h => isContr_paths (pmap_dom_isContr A B c) _ _).

  Definition pcomp_assoc_lemma {X Y Z : Type} (F : Y -> Z) (G : X -> Y)
    {a b : X} (p : a = b) {y : Y} {z : Z} (q : y = G a) (r : z = F y)
    : ap (fun x => F (G x)) p ⋅ (ap F q ⋅ r) = ap F (ap G p ⋅ q) ⋅ r.
  Proof. destruct p. exact refl. Defined.

  Definition pcomp_assoc {W X Y Z : Ustar} (f : Y →* Z) (g : X →* Y) (h : W →* X)
    : pcomp (pcomp f g) h = pcomp f (pcomp g h)
    := ap (fun r => ((fun w => fst f (fst g (fst h w))); r) : W →* Z)
          (pcomp_assoc_lemma (fst f) (fst g) (snd h) (snd g) (snd f)).

  Definition unitStar : Ustar := (True; tt).

  Definition True_isContr : isContr True := (tt; fun t => match t with tt => refl end).

  Definition univCovering_contr {A B : Ustar} (f : A →* B)
    (gB : isGrpd (utype B)) (cf : isPtdCovering f) (u : isUnivCovering f)
    : isContr (utype A).
  Proof.
    pose (cstp := ((fun _ => pt B); refl) : unitStar →* B).
    pose (hc := fst (u unitStar cstp (cst_covering gB (pt B)))).
    pose (hc' := fst (contr_univCovering cstp True_isContr A f cf)).
    pose (h := fst hc). pose (h' := fst hc').
    pose (e := snd hc @ ap (fun k => pcomp k h) (snd hc') @ pcomp_assoc f h' h
               : f = pcomp f (pcomp h' h)).
    pose (cu := u A f cf).
    pose (r := ap fst ((snd cu ((pid A; refl) : {k : A →* A & f = pcomp f k}))^
                       @ snd cu (pcomp h' h; e))
               : pid A = pcomp h' h).
    refine (fst h' tt; fun a => _).
    exact (ap (fst h') (True_isProp tt (fst h a)) @ (ptw (ap fst r) a)^).
  Defined.

End UnivCoverOfGroupoid.

(** Definition [def:RtoS1]: [R(base) :≡ ℤ], [R(loop) := etop(zs)], and the
    exponential covering [exp :≡ fst : Tot(R) → S1], pointed at
    [(base, 0)] with pointing path [refl]. *)
Section ExpCovering.

  Context `{Univalence}.

  Definition R : S1 -> Type := S1_rec Type ℤ (etop zsEqv).

  Definition R_isSet (z : S1) : isSet (R z)
    := ptrunc_rec (isSet_isProp _)
         (fun p : base = z => trp (fun x => isSet (R x)) p ℤ_isSet)
         (S1_base_paths z).

  Definition RSet : S1 -> SetU := fun z => (R z; R_isSet z).

  Definition TotRstar : Ustar := (Tot R; (base; iplus 0)).

  (** The implicit arguments of [fst] are given explicitly: otherwise
      unification unfolds [R] into a case analysis on the library's private
      inductive type underlying [S1]. *)
  Definition exp : TotRstar →* S1star := (@fst S1 R; refl).

  Definition exp_covering : isPtdCovering exp
    := fun z => is_ntype_Eqv 0 (fst_fiber_eqv R z) (R_isSet z).

End ExpCovering.
