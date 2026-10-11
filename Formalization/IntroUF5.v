(** * Formalization of Sections 2.19 - 2.21 of [intro-uf.tex]

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

From HoTT Require Import Basics Types.Sigma Types.Equiv Types.Bool
  Types.Universe Types.Forall Truncations.Core.
From SymmetryMirror Require Import IntroUF IntroUF2 IntroUF3 Bridge IntroUF4.

Local Open Scope uf_scope.

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
  pose (Re := mkEqv
    (fun v : {Y : Ustar & (A; a) ≃* Y} =>
       ((fst (fst v); (fst (fst (snd v)); snd (snd v))) : {B : Type & A ≃ B};
        (snd (fst v); snd (fst (snd v)))))
    (fun u : {w : {B : Type & A ≃ B} & {b : fst w & b = fst (snd w) a}} =>
       ((fst (fst u); fst (snd u)) : Ustar;
        ((fst (snd (fst u)); snd (snd u)); snd (snd (fst u)))))
    (fun _ => refl) (fun _ => refl)).
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
