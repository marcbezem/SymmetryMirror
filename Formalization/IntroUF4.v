(** * Formalization of Sections 2.16 - 2.18 of [intro-uf.tex]

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

From HoTT Require Import Basics Types.Sigma Types.Equiv Types.Bool
  Types.Universe Truncations.Core.
From SymmetryMirror Require Import IntroUF IntroUF2 IntroUF3 Bridge.

Local Open Scope uf_scope.

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
