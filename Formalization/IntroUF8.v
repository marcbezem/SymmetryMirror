(** * Formalization of Sections 2.25 - 2.27 of [intro-uf.tex]

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

From HoTT Require Import Basics Types.Sigma Types.Equiv Types.Universe
  Types.Forall Truncations.Core Truncations.SeparatedTrunc
  Universes.TruncType Spaces.Finite.Fin.
From SymmetryMirror Require Import IntroUF IntroUF2 IntroUF3 Bridge IntroUF4
  IntroUF5 IntroUF6 IntroUF7.

Local Open Scope uf_scope.

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
