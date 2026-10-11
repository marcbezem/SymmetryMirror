(** * Formalization of Sections 2.7 - 2.12 of [intro-uf.tex]

    Continuation of [IntroUF.v]; the same conventions apply:
    1. path composition in function-composition order, [q ⋅ p :≡ p ∙ q],
       with [trans] defined by induction on the second argument;
    2. fibers are defined using [y = f x]: [f⁻¹(y) :≡ ∑_{x:X} (y = f x)];
    3. [ptw] is Book HoTT's [happly], for dependent functions.

    Sum types are Coq-HoTT's [sig], written [{x : X & Y x}], with pairs
    [(x; y)] and projections [pr1], [pr2] (the book's [fst] and [snd]).
    The record [sig] has primitive projections, hence definitional eta,
    which makes many round trips below hold by definition.

    Where the book refers to the HoTT Book for a proof (the converse of
    [lem:weq-iso], and [lem:fiberwise-equiv-from-tot]), we use the
    corresponding results of Coq-HoTT, via a bridge between the book's
    [isEq] and Coq-HoTT's [IsEquiv]. *)

From HoTT Require Import Basics Types.Sigma Types.Equiv Types.Bool.
From SymmetryMirror Require Import IntroUF.

Local Open Scope uf_scope.

(** ** 2.7 Identifying elements in members of families of types *)

(** Definition [def:pathsoverpaths]: the type [y =^Y_p y'] of paths from
    [y] to [y'] over [p], by induction on [p]. *)
Definition PathOver {X : Type} (Y : X -> Type) {a a' : X} (p : a = a')
  : Y a -> Y a' -> Type
  := match p with idpath => fun y y' => y = y' end.

Definition PathOver_refl {X : Type} (Y : X -> Type) {a : X} (y y' : Y a)
  : PathOver Y idpath y y' = (y = y') := idpath.

(** Remark: for a constant family the types of paths over [p] and of
    paths can be identified, by induction on [p].  (This is an
    identification of types, no univalence is needed.) *)
Definition PathOver_const {X Z : Type} {a a' : X} (p : a = a') (z z' : Z)
  : PathOver (fun _ => Z) p z z' = (z = z').
Proof. destruct p. exact idpath. Defined.

(** Definition [def:pathover-trp]: [po_p : (y =^Y_p y') = (trp^Y_p(y) = y')]. *)
Definition po {X : Type} {Y : X -> Type} {a a' : X} (p : a = a')
  (y : Y a) (y' : Y a') : PathOver Y p y y' = (trp Y p y = y').
Proof. destruct p. exact idpath. Defined.

(** Definition [def:pathovercomposition]: composition of paths over paths,
    by induction on [p'] and then on [q']. *)
Definition po_comp {X : Type} {Y : X -> Type} {x x' x'' : X}
  {p : x = x'} {p' : x' = x''} {y : Y x} {y' : Y x'} {y'' : Y x''}
  (q' : PathOver Y p' y' y'') (q : PathOver Y p y y')
  : PathOver Y (p' ⋅ p) y y''.
Proof. destruct p'. cbn in q'. destruct q'. exact q. Defined.

Notation "q' ⊙ q" := (po_comp q' q) (at level 40, left associativity) : uf_scope.

(** The inverse of a path over a path. *)
Definition po_inv {X : Type} {Y : X -> Type} {x x' : X} {p : x = x'}
  {y : Y x} {y' : Y x'} (q : PathOver Y p y y') : PathOver Y p⁻¹ y' y.
Proof. destruct p. cbn in q. destruct q. exact idpath. Defined.

(** Exercise [xca:cp]: some groupoid laws for paths over paths.  Where the
    paths underneath are not equal by definition, we transport along the
    corresponding law from [xca:path-groupoid-laws]. *)
Section PathOverLaws.

  Context {X : Type} {Y : X -> Type} {x x' : X} {p : x = x'}
    {y : Y x} {y' : Y x'} (q : PathOver Y p y y').

  Definition po_comp_1q : (idpath : PathOver Y idpath y' y') ⊙ q = q
    := idpath.

  Definition po_comp_q1
    : trp (fun r => PathOver Y r y y') (trans_1p p)
        (q ⊙ (idpath : PathOver Y idpath y y)) = q.
  Proof. destruct p. cbn in q. destruct q. exact idpath. Defined.

  Definition po_comp_Vq
    : trp (fun r => PathOver Y r y y) (trans_pV p) (po_inv q ⊙ q) = idpath.
  Proof. destruct p. cbn in q. destruct q. exact idpath. Defined.

  Definition po_inv_inv
    : trp (fun r => PathOver Y r y y') (symm_symm p) (po_inv (po_inv q)) = q.
  Proof. destruct p. cbn in q. destruct q. exact idpath. Defined.

End PathOverLaws.

(** Definition [def:apd]: dependent application of [f] to paths. *)
Definition apd' {X : Type} {Y : X -> Type} (f : forall x, Y x)
  {x x' : X} (p : x = x') : PathOver Y p (f x) (f x')
  := match p with idpath => idpath end.

(** Definition [def:applfun2]: application of a function of two variables
    to a path and a path over it. *)
Definition apap {X Z : Type} {Y : X -> Type} (g : forall x, Y x -> Z)
  {x x' : X} {y : Y x} {y' : Y x'} (p : x = x') (q : PathOver Y p y y')
  : g x y = g x' y'.
Proof. destruct p. cbn in q. destruct q. exact idpath. Defined.

(** Definition [def:applfun2comp]. *)
Definition apap_refl {X Z : Type} {Y : X -> Type} (g : forall x, Y x -> Z)
  {x : X} {y y' : Y x} (q : y = y')
  : apap g idpath q = ap' (g x) q
  := match q with idpath => idpath end.

(** ** 2.8 Sum types

    The sum type [∑_{x:X} Y(x)] is [{x : X & Y x}], also denoted [Tot(Y)].
    If [X] and [Y(x)] are in [U], then so is the sum. *)

Notation Tot Y := (sig Y).

Definition sum_in_U@{u} (X : Type@{u}) (Y : X -> Type@{u}) : Type@{u}
  := {x : X & Y x}.

(** First and second projection: [fst(a,b) :≡ a] and [snd(a,b) :≡ b]. *)
Definition fst_jdeq {X : Type} {Y : X -> Type} (a : X) (b : Y a)
  : pr1 (a; b) = a := idpath.
Definition snd_jdeq {X : Type} {Y : X -> Type} (a : X) (b : Y a)
  : pr2 (a; b) = b := idpath.

Check (@pr2 : forall {X : Type} {Y : X -> Type} (z : {x : X & Y x}), Y (pr1 z)).

(** Remark [rem:non-dependent-sums]: the binary product [X × Y] is the sum
    over a constant family (see 2.11).  Remark [rem:iterated-sums]:
    [(x, y, z) :≡ (x, (y, z))]. *)
Definition triple {X : Type} {Y : X -> Type} {Z : forall x, Y x -> Type}
  (x : X) (y : Y x) (z : Z x y) : {x : X & {y : Y x & Z x y}}
  := (x; y; z).

(** ** 2.9 Equivalences *)

(** Definition [def:contractible]. *)
Definition iscontr (X : Type) : Type := {c : X & forall x : X, c = x}.

(** Any element of a contractible type can serve as the center. *)
Definition iscontr_center {X : Type} (H : iscontr X) (a : X)
  : forall x : X, a = x
  := fun x => pr2 H x ⋅ (pr2 H a)⁻¹.

(** Lemma [lem:thepathspaceiscontractible]: singleton types are
    contractible. *)
Definition singleton_contr {X : Type} (a : X) : iscontr {x : X & a = x}.
Proof.
  exists (a; idpath).
  intros [x i]. destruct i. exact idpath.
Defined.

(** Definition [def:fiber], with the convention [y = f x]. *)
Definition fiber {X Y : Type} (f : X -> Y) (y : Y) : Type
  := {x : X & y = f x}.

(** Definition [def:equivalence]. *)
Definition isEq {X Y : Type} (f : X -> Y) : Type
  := forall y : Y, iscontr (fiber f y).

(** Definition [def:type-of-equivalences]. *)
Definition Eqv (X Y : Type) : Type := {f : X -> Y & isEq f}.

Notation "X ≃ Y" := (Eqv X Y) (at level 85) : uf_scope.

(** The inverse of an equivalence: [g(y) :≡ fst(fst(t(y)))]. *)
Section Inverse.

  Context {X Y : Type} {f : X -> Y} (t : isEq f).

  Definition eqinv : Y -> X := fun y => pr1 (pr1 (t y)).

  Definition eqinv_r (y : Y) : f (eqinv y) = y := (pr2 (pr1 (t y)))⁻¹.

  Definition eqinv_l (x : X) : eqinv (f x) = x
    := ap' pr1 (pr2 (t (f x)) (x; idpath)).

End Inverse.

(** The identity function is an equivalence: its fibers are singletons
    (by definition, thanks to the convention [y = f x]). *)
Definition id_isEq (X : Type) : isEq (id X) := fun a => singleton_contr a.

(** Transport is an equivalence. *)
Definition trp_isEq {X : Type} (T : X -> Type) {x y : X} (e : x = y)
  : isEq (trp T e)
  := match e with idpath => id_isEq (T x) end.

(** *** Bridge to Coq-HoTT's [IsEquiv] *)

(** Contractibility is preserved by retracts. *)
Definition iscontr_retract {A B : Type} (r : A -> B) (s : B -> A)
  (rs : forall b, r (s b) = b) : iscontr A -> iscontr B.
Proof.
  intros [c h]. exists (r c).
  intro b. exact (rs b ⋅ ap' r (h (s b))).
Defined.

Definition isEq_of_IsEquiv {X Y : Type} (f : X -> Y) `{IsEquiv X Y f}
  : isEq f.
Proof.
  intro y.
  refine (iscontr_retract (A := hfiber f y) (B := fiber f y)
            (fun w => (pr1 w; (pr2 w)^)) (fun w => (pr1 w; (pr2 w)^)) _ _).
  - intros [x p]. cbn. exact (ap (fun q => (x; q)) (inv_V p)).
  - exact (center (hfiber f y); contr).
Defined.

Definition IsEquiv_of_isEq {X Y : Type} {f : X -> Y} (t : isEq f)
  : IsEquiv f
  := isequiv_adjointify f (eqinv t) (eqinv_r t) (eqinv_l t).

(** Construction [lem:weq-iso]. *)
Definition isEq_to_iso {X Y : Type} {f : X -> Y} (t : isEq f)
  : {g : Y -> X & (forall x, g (f x) = x) * (forall y, f (g y) = y)}
  := (eqinv t; (eqinv_l t, eqinv_r t)).

Definition iso_to_isEq {X Y : Type} (f : X -> Y) (g : Y -> X)
  (gf : forall x, g (f x) = x) (fg : forall y, f (g y) = y) : isEq f
  := isEq_of_IsEquiv f (H := isequiv_adjointify f g fg gf).

Definition mkEqv {X Y : Type} (f : X -> Y) (g : Y -> X)
  (gf : forall x, g (f x) = x) (fg : forall y, f (g y) = y) : X ≃ Y
  := (f; iso_to_isEq f g gf fg).

Definition Eqv_of_Equiv {X Y : Type} (e : X <~> Y) : X ≃ Y
  := (equiv_fun e; isEq_of_IsEquiv e).

(** Exercise [xca:equivalence-invers]. *)
Definition eqinv_isEq {X Y : Type} {f : X -> Y} (t : isEq f)
  : isEq (eqinv t)
  := iso_to_isEq (eqinv t) f (eqinv_r t) (eqinv_l t).

Definition Eqv_inv {X Y : Type} : (X ≃ Y) -> (Y ≃ X)
  := fun e => (eqinv (pr2 e); eqinv_isEq (pr2 e)).

(** Exercise [xca:equivalence-comp]. *)
Definition comp_isEq {X Y Z : Type} {f : X -> Y} {g : Y -> Z}
  (s : isEq f) (t : isEq g) : isEq (comp g f).
Proof.
  refine (iso_to_isEq _ (comp (eqinv s) (eqinv t)) _ _); intro; unfold comp.
  - exact (ap (eqinv s) (eqinv_l t _) @ eqinv_l s _).
  - exact (ap g (eqinv_r s _) @ eqinv_r t _).
Defined.

Definition Eqv_comp {X Y Z : Type} : (X ≃ Y) -> ((Y ≃ Z) -> (X ≃ Z))
  := fun e e' => (comp (pr1 e') (pr1 e); comp_isEq (pr2 e) (pr2 e')).

(** Exercise [xca:2-out-of-3], with [e : hf = g]. *)
Section TwoOutOfThree.

  Context {A B C : Type} (f : A -> B) (g : A -> C) (h : B -> C)
    (e : comp h f = g).

  Let E (a : A) : h (f a) = g a := ptw e a.

  Definition two_of_three_g (sf : isEq f) (sh : isEq h) : isEq g.
  Proof.
    refine (iso_to_isEq g (comp (eqinv sf) (eqinv sh)) _ _); intro; unfold comp.
    - exact (ap (fun c => eqinv sf (eqinv sh c)) (E _)^
               @ ap (eqinv sf) (eqinv_l sh _) @ eqinv_l sf _).
    - exact ((E _)^ @ ap h (eqinv_r sf _) @ eqinv_r sh _).
  Defined.

  Definition two_of_three_h (sf : isEq f) (sg : isEq g) : isEq h.
  Proof.
    refine (iso_to_isEq h (comp f (eqinv sg)) _ _); intro b; unfold comp.
    - exact (ap (fun c => f (eqinv sg c))
               (ap h (eqinv_r sf b)^ @ E (eqinv sf b))
             @ ap f (eqinv_l sg _) @ eqinv_r sf b).
    - exact (E _ @ eqinv_r sg b).
  Defined.

  Definition two_of_three_f (sg : isEq g) (sh : isEq h) : isEq f.
  Proof.
    refine (iso_to_isEq f (comp (eqinv sg) h) _ _); intro b; unfold comp.
    - exact (ap (eqinv sg) (E b) @ eqinv_l sg b).
    - exact ((eqinv_l sh _)^
             @ ap (eqinv sh) (E _ @ eqinv_r sg (h b)) @ eqinv_l sh b).
  Defined.

End TwoOutOfThree.

(** Lemma [lem:contract-away]. *)
Section ContractAway.

  Context {X : Type} (a : X) (B : forall x, a = x -> Type).

  Definition ca_map : {x : X & {i : a = x & B x i}} -> B a idpath
    := fun w => path_ind a (fun x i => B x i -> B a idpath) (id _)
                  (pr1 w) (pr1 (pr2 w)) (pr2 (pr2 w)).

  Definition ca_map_isEq : isEq ca_map.
  Proof.
    refine (iso_to_isEq ca_map (fun b => (a; idpath; b)) _ _).
    - intros [x [i b]]. destruct i. exact idpath.
    - intro b. exact idpath.
  Defined.

End ContractAway.

(** Corollary [cor:contract-away]; here [(a = x) × B(x)] is the sum over
    a constant family, see 2.11. *)
Definition contract_away {X : Type} (a : X) (B : X -> Type)
  : {x : X & {_ : a = x & B x}} ≃ B a
  := (ca_map a (fun x _ => B x); ca_map_isEq a (fun x _ => B x)).

(** Exercise [xca:sum-equiv-base]. *)
Definition sum_equiv_base {X Y : Type} {f : X -> Y} (t : isEq f)
  (B : X -> Type) : {x : X & B x} ≃ {y : Y & B (eqinv t y)}
  := Eqv_of_Equiv (equiv_inverse
       (equiv_functor_sigma_pb (Q := B)
          (Build_Equiv _ _ (eqinv t) (IsEquiv_of_isEq (eqinv_isEq t))))).

(** Definition [def:fiberwise]: totalization of a map of families. *)
Definition tot {X : Type} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  : Tot Y -> Tot Z
  := fun w => (pr1 w; f (pr1 w) (pr2 w)).

(** Lemma [lem:fiberwise] and Exercise [xca:fiberwise]. *)
Definition tot_isEq {X : Type} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  (t : forall x, isEq (f x)) : isEq (tot f).
Proof.
  refine (iso_to_isEq (tot f) (tot (fun x => eqinv (t x))) _ _).
  - intros [x y]. exact (ap' (fun y' => (x; y')) (eqinv_l (t x) y)).
  - intros [x z]. exact (ap' (fun z' => (x; z')) (eqinv_r (t x) z)).
Defined.

(** Lemma [lem:fiberwise-equiv-from-tot] (Theorem 4.7.7 of the HoTT Book). *)
Definition isEq_from_tot {X : Type} {Y Z : X -> Type}
  (f : forall x, Y x -> Z x) (t : isEq (tot f)) : forall x, isEq (f x)
  := fun x => isEq_of_IsEquiv (f x)
       (H := @isequiv_from_functor_sigma X Y Z f (IsEquiv_of_isEq t) x).

(** Principle [def:funext]: function extensionality postulates
    [funext : isEq(ptw_{f,g})].  We derive it from Coq-HoTT's axiom
    [Funext], which states that [apD10] is an equivalence. *)
Definition funext `{Funext} {X : Type} {Y : X -> Type} (f g : forall x, Y x)
  : isEq (@ptw X Y f g)
  := isEq_of_IsEquiv ptw
       (H := isequiv_homotopic apD10 (fun p => (ptw_is_apD10 p)^)).

Definition ptw_inv `{Funext} {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  : (forall x, f x = g x) -> f = g
  := eqinv (funext f g).

(** Exercise [xca:substitute-away]. *)
Definition substitute_away `{Funext} {X : Type} (a : X) (B : X -> Type)
  : (forall x, a = x -> B x) ≃ B a.
Proof.
  refine (mkEqv (fun h => h a idpath) (fun b x i => trp B i b) _ _).
  - intro h. apply ptw_inv; intro x. apply ptw_inv; intro i.
    destruct i. exact idpath.
  - intro b. exact idpath.
Defined.

(** Exercise [xca:Xequiv1toX]. *)
Definition unit_to_X_eqv `{Funext} (X : Type) : (Unit -> X) ≃ X.
Proof.
  refine (mkEqv (fun f => f tt) (fun x => cst x) _ _).
  - intro f. apply ptw_inv. intros []. exact idpath.
  - intro x. exact idpath.
Defined.

(** Exercise [xca:XequivXtimes1]. *)
Definition sum_unit_eqv (X : Type) : {_ : X & Unit} ≃ X.
Proof.
  refine (mkEqv pr1 (fun x => (x; tt)) _ _).
  - intros [x []]. exact idpath.
  - intro x. exact idpath.
Defined.

(** Exercise [xca:Sigma-distrib]. *)
Definition sigma_distrib (X Y : Type) (Z : Y -> Type)
  : {_ : X & {y : Y & Z y}} ≃ {y : Y & {_ : X & Z y}}
  := mkEqv (fun w : {_ : X & {y : Y & Z y}} => (pr1 (pr2 w); pr1 w; pr2 (pr2 w)))
           (fun w : {y : Y & {_ : X & Z y}} => (pr1 (pr2 w); pr1 w; pr2 (pr2 w)))
           (fun _ => idpath) (fun _ => idpath).

(** Exercise [xca:Sigma-comm]. *)
Definition sigma_comm (X Y : Type) (Z : X -> Y -> Type)
  : {x : X & {y : Y & Z x y}} ≃ {y : Y & {x : X & Z x y}}
  := mkEqv (fun w : {x : X & {y : Y & Z x y}} => (pr1 (pr2 w); pr1 w; pr2 (pr2 w)))
           (fun w : {y : Y & {x : X & Z x y}} => (pr1 (pr2 w); pr1 w; pr2 (pr2 w)))
           (fun _ => idpath) (fun _ => idpath).

(** Footnote [ft:Sigma-assoc]: associativity of sum types. *)
Definition sigma_assoc (X : Type) (Y : X -> Type)
  (Z : forall x, Y x -> Type)
  : {x : X & {y : Y x & Z x y}} ≃ {w : {x : X & Y x} & Z (pr1 w) (pr2 w)}
  := mkEqv (fun w : {x : X & {y : Y x & Z x y}} =>
              ((pr1 w; pr1 (pr2 w)) : {x : X & Y x}; pr2 (pr2 w)))
           (fun w : {w : {x : X & Y x} & Z (pr1 w) (pr2 w)} =>
              (pr1 (pr1 w); pr2 (pr1 w); pr2 w))
           (fun _ => idpath) (fun _ => idpath).

(** Exercise [xca:fib-of-comp]. *)
Definition fib_of_comp {X Y Z : Type} (f : X -> Y) (g : Y -> Z) (z : Z)
  : fiber (comp g f) z ≃ {w : fiber g z & fiber f (pr1 w)}.
Proof.
  refine (mkEqv (fun v : fiber (comp g f) z =>
                   ((f (pr1 v); pr2 v) : fiber g z; (pr1 v; idpath) : fiber f _))
                (fun w : {w : fiber g z & fiber f (pr1 w)} =>
                   (pr1 (pr2 w); ap' g (pr2 (pr2 w)) ⋅ pr2 (pr1 w)))
                (fun _ => idpath) _).
  intros [[y p] [x q]]. cbn in *.
  revert y q p. refine (paths_ind_r _ _ _). intro p. exact idpath.
Defined.

(** Exercise [xca:AC-in-TT]: holds with round trips by definition. *)
Definition type_theoretic_AC (X Y : Type) (Z : X -> Y -> Type)
  : (forall x, {y : Y & Z x y}) ≃ {f : X -> Y & forall x, Z x (f x)}
  := mkEqv (fun h : forall x, {y : Y & Z x y} =>
              ((fun x => pr1 (h x)); (fun x => pr2 (h x)))
              : {f : X -> Y & forall x, Z x (f x)})
           (fun w : {f : X -> Y & forall x, Z x (f x)} =>
              fun x => (pr1 w x; pr2 w x) : {y : Y & Z x y})
           (fun _ => idpath) (fun _ => idpath).

(** Exercise [xca:section-above-f]. *)
Section SectionAboveF.

  Context {X Z : Type} {Y : X -> Type} (f : Z -> X).

  Let fwd (s : forall z, Y (f z))
    : {g : Z -> {x : X & Y x} & f = comp pr1 g}
    := ((fun z => (f z; s z)); idpath).

  Let bwd (w : {g : Z -> {x : X & Y x} & f = comp pr1 g})
    : forall z, Y (f z)
    := fun z => trp Y (ptw (pr2 w) z)⁻¹ (pr2 (pr1 w z)).

  Local Definition fwd_bwd_gen (g1 : Z -> X) (g2 : forall z, Y (g1 z))
    (e : f = g1)
    : fwd (bwd ((fun z => (g1 z; g2 z)); e)) = ((fun z => (g1 z; g2 z)); e).
  Proof. destruct e. exact idpath. Defined.

  Definition section_above_f
    : (forall z, Y (f z)) ≃ {g : Z -> {x : X & Y x} & f = comp pr1 g}.
  Proof.
    refine (mkEqv fwd bwd (fun _ => idpath) _).
    intros [g e]. exact (fwd_bwd_gen (comp pr1 g) (fun z => pr2 (g z)) e).
  Defined.

End SectionAboveF.

(** Exercise [xca:Sigma-curry]. *)
Definition sigma_curry (X Z : Type) (Y : X -> Type)
  : ({x : X & Y x} -> Z) ≃ (forall x, Y x -> Z)
  := mkEqv (fun (h : {x : X & Y x} -> Z) x y => h (x; y))
           (fun (k : forall x, Y x -> Z) (w : {x : X & Y x}) => k (pr1 w) (pr2 w))
           (fun _ => idpath) (fun _ => idpath).

(** ** 2.10 Identifying pairs *)

Section IdentifyingPairs.

  Context {X : Type} {Y : X -> Type}.

  (** Definition [def:pairtopath]. *)
  Definition pair : forall x : X, Y x -> Tot Y := fun x y => (x; y).

  Definition pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y') : (x; y) = (x'; y')
    := apap pair p q.

  (** Construction [cor:isEq-pair=]. *)
  Definition pathpair_refl {x : X} {y y' : Y x} (q : y = y')
    : pathpair idpath q = ap' (pair x) q
    := apap_refl pair q.

  (** The inverse map [Ψ], for arbitrary elements of the sum type. *)
  Definition pathsplit {w w' : Tot Y} (r : w = w')
    : {p : pr1 w = pr1 w' & PathOver Y p (pr2 w) (pr2 w')}
    := match r with idpath => (idpath; idpath) end.

  Definition pathsplit_pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y')
    : pathsplit (pathpair p q) = (p; q).
  Proof. destruct p. cbn in q. destruct q. exact idpath. Defined.

  Definition pathpair_pathsplit {w w' : Tot Y} (r : w = w')
    : pathpair (pr1 (pathsplit r)) (pr2 (pathsplit r)) = r.
  Proof. destruct r. exact idpath. Defined.

  (** Lemma [lem:isEq-pair=]. *)
  Definition pathpair_isEq {x x' : X} {y : Y x} {y' : Y x'}
    : isEq (fun pq : {p : x = x' & PathOver Y p y y'} =>
              pathpair (pr1 pq) (pr2 pq))
    := iso_to_isEq _ pathsplit
         (fun pq => pathsplit_pathpair (pr1 pq) (pr2 pq))
         pathpair_pathsplit.

  Definition path_sigma_eqv {x x' : X} {y : Y x} {y' : Y x'}
    : {p : x = x' & PathOver Y p y y'} ≃ ((x; y) = (x'; y'))
    := (_; pathpair_isEq).

  (** [fst(pair^=(p,q)) = p], [snd(pair^=(p,q)) = q] (combined in
      [pathsplit_pathpair] above), and [r = pair^=(fst(r), snd(r))]
      (this is [pathpair_pathsplit]). *)
  Definition ap_pr1_pathpair {x x' : X} {y : Y x} {y' : Y x'}
    (p : x = x') (q : PathOver Y p y y')
    : ap' pr1 (pathpair p q) = p.
  Proof. destruct p. cbn in q. destruct q. exact idpath. Defined.

  Definition pr1_pathsplit {w w' : Tot Y} (r : w = w')
    : pr1 (pathsplit r) = ap' pr1 r
    := match r with idpath => idpath end.

End IdentifyingPairs.

(** ** 2.11 Binary products

    The binary product [X × Y] is the sum over the constant family [Y]. *)

Notation "X × Y" := ({_ : X & Y})
  : uf_scope.

(** It is equivalent to Coq-HoTT's record type [prod]. *)
Definition binprod_prod (X Y : Type) : (X × Y) ≃ (X * Y)
  := mkEqv (fun w : X × Y => (pr1 w, pr2 w)) (fun w : X * Y => (fst w; snd w) : X × Y)
           (fun _ => idpath) (fun _ => idpath).

(** Paths over a path in a constant family are paths, as an equivalence. *)
Definition po_const {X Z : Type} {a a' : X} (p : a = a') {z z' : Z}
  : (z = z') -> PathOver (fun _ => Z) p z z'
  := match p with idpath => id _ end.

Definition po_const_isEq {X Z : Type} {a a' : X} (p : a = a') (z z' : Z)
  : isEq (@po_const X Z a a' p z z')
  := match p with idpath => id_isEq _ end.

(** Lemma [lem:isEq-pair-bin=]. *)
Definition pathpair_bin {X Y : Type} {x x' : X} {y y' : Y}
  : (x = x') × (y = y') -> ((x; y) = (x'; y') :> X × Y)
  := fun pq => pathpair (pr1 pq) (po_const (pr1 pq) (pr2 pq)).

Definition pathpair_bin_isEq {X Y : Type} {x x' : X} {y y' : Y}
  : isEq (@pathpair_bin X Y x x' y y')
  := comp_isEq (tot_isEq _ (fun p => po_const_isEq p y y')) pathpair_isEq.

Definition path_prod_eqv {X Y : Type} (x x' : X) (y y' : Y)
  : ((x = x') × (y = y')) ≃ ((x; y) = (x'; y') :> X × Y)
  := (_; pathpair_bin_isEq).

(** The product of two maps. *)
Definition prod_map {X X' Y Y' : Type} (f : X -> Y) (f' : X' -> Y')
  : X × X' -> Y × Y'
  := fun w => (f (pr1 w); f' (pr2 w)).

(** Booleans: the book's [yes] and [no] are [true] and [false]. *)
Notation yes := true.
Notation no := false.

(** Exercise [xca:binary-prod-equiv]. *)
Definition bool_family (X Y : Type) : Bool -> Type
  := fun b => if b then Y else X.

Definition binary_prod_equiv `{Funext} (X Y : Type)
  : isEq (fun f : forall b, bool_family X Y b => (f no; f yes) : X × Y).
Proof.
  refine (iso_to_isEq _
            (fun (w : X × Y) b => match b return bool_family X Y b with
                                  | yes => pr2 w | no => pr1 w end)
            _ (fun _ => idpath)).
  intro f. apply ptw_inv. intros []; exact idpath.
Defined.

(** Exercise [xca:binary-prod-comm]. *)
Definition binary_prod_comm (X Y : Type) : (X × Y) ≃ (Y × X)
  := mkEqv (fun w : X × Y => (pr2 w; pr1 w) : Y × X)
           (fun w : Y × X => (pr2 w; pr1 w) : X × Y)
           (fun _ => idpath) (fun _ => idpath).

(** ** 2.12 More inductive types *)

(** *** Finite types: [Empty] ([𝟘]), [Unit] ([𝟙] with [triv :≡ tt]) and
    [Bool] ([𝟚]), all in [Type0]. *)

Check (Empty : Type0).
Check (Unit : Type0).
Check (Bool : Type0).

Definition Empty_paths (x y : Empty) : x = y := match x with end.

Definition Empty_absurd_nat : Empty -> (0%nat = 1%nat)
  := fun x => match x with end.

Definition Unit_center (u : Unit) : u = tt
  := match u with tt => idpath end.

Definition Unit_paths (x y : Unit) : x = y
  := match x, y with tt, tt => idpath end.

Definition to_Unit (X : Type) : X -> Unit := fun _ => tt.

(** Exercise [xca:True-univ-prop]. *)
Definition unit_univ_prop `{Funext} (X : Type)
  : isEq (fun f : Unit -> X => f tt)
  := pr2 (unit_to_X_eqv X).

(** [(yes = no) -> 𝟘], by substitution in [P(yes) :≡ 𝟙], [P(no) :≡ 𝟘]. *)
Definition yes_ne_no : (yes = no) -> Empty
  := fun e => trp (fun b : Bool => if b then Unit else Empty) e tt.

(** [(0 = S(n)) -> 𝟘], by substitution in [P(0) :≡ 𝟙], [P(S(m)) :≡ 𝟘]. *)
Definition zero_ne_succ (n : nat) : (0%nat = S n) -> Empty
  := fun e => trp (fun i : nat => match i with O => Unit | S _ => Empty end)
                e tt.

(** *** Binary sums: [X ⨿ Y] is Coq-HoTT's [X + Y]. *)

Notation "X ⨿ Y" := (sum X Y) (at level 50, left associativity) : uf_scope.

(** Exercise [xca:binary-sum-equiv]. *)
Definition binary_sum_equiv (X Y : Type)
  : isEq (fun z : X ⨿ Y =>
            match z return {b : Bool & bool_family X Y b} with
            | inl x => (no; x)
            | inr y => (yes; y)
            end).
Proof.
  refine (iso_to_isEq _
            (fun w => match w with
                      | (yes; y) => inr y
                      | (no; x) => inl x
                      end) _ _).
  - intros [x|y]; exact idpath.
  - intros [[] t]; exact idpath.
Defined.

(** Exercise [xca:binary-sum-id].  We use the encode-decode method instead
    of the suggested route via [xca:binary-sum-equiv]. *)
Section BinarySumPaths.

  Context {X Y : Type}.

  Definition code_inl (x : X) : X ⨿ Y -> Type
    := fun w => match w with inl x' => x = x' | inr _ => Empty end.

  Definition code_inr (y : Y) : X ⨿ Y -> Type
    := fun w => match w with inl _ => Empty | inr y' => y = y' end.

  Definition encode_inl {x : X} {w : X ⨿ Y} (r : inl x = w) : code_inl x w
    := trp (code_inl x) r idpath.

  Definition encode_inr {y : Y} {w : X ⨿ Y} (r : inr y = w) : code_inr y w
    := trp (code_inr y) r idpath.

  Definition inl_ne_inr (x : X) (y : Y) : (inl x = inr y) -> Empty
    := encode_inl.

  Definition path_inl_eqv (x x' : X) : (inl x = inl x' :> X ⨿ Y) ≃ (x = x').
  Proof.
    refine (mkEqv (@encode_inl x (inl x')) (ap' inl) _ _).
    - intro r.
      enough (G : forall w (r : inl x = w),
                 match w return inl x = w -> Type with
                 | inl x' => fun r => ap' inl (encode_inl r) = r
                 | inr _ => fun _ => Unit
                 end r) by exact (G _ r).
      intros w r'. destruct r'. exact idpath.
    - intro p. destruct p. exact idpath.
  Defined.

  Definition path_inr_eqv (y y' : Y) : (inr y = inr y' :> X ⨿ Y) ≃ (y = y').
  Proof.
    refine (mkEqv (@encode_inr y (inr y')) (ap' inr) _ _).
    - intro r.
      enough (G : forall w (r : inr y = w),
                 match w return inr y = w -> Type with
                 | inl _ => fun _ => Unit
                 | inr y' => fun r => ap' inr (encode_inr r) = r
                 end r) by exact (G _ r).
      intros w r'. destruct r'. exact idpath.
    - intro p. destruct p. exact idpath.
  Defined.

End BinarySumPaths.

(** Exercise [xca:bin-sum-univ-prop]. *)
Definition bin_sum_univ_prop `{Funext} (X Y Z : Type)
  : isEq (fun h : X ⨿ Y -> Z => (comp h inl; comp h inr) : (X -> Z) × (Y -> Z)).
Proof.
  refine (iso_to_isEq _
            (fun (w : (X -> Z) × (Y -> Z)) z =>
               match z with inl x => pr1 w x | inr y => pr2 w y end)
            _ (fun _ => idpath)).
  intro h. apply ptw_inv. intros [x|y]; exact idpath.
Defined.

(** Exercise: [(X ⨿ 𝟘) ≃ X]. *)
Definition sum_empty_eqv (X : Type) : (X ⨿ Empty) ≃ X.
Proof.
  refine (mkEqv (fun z : X ⨿ Empty =>
                   match z with inl x => x | inr e => match e with end end)
                inl _ (fun _ => idpath)).
  intros [x|[]]. exact idpath.
Defined.

(** *** Unary sums *)

Inductive Copy (X : Type) : Type := inc : X -> Copy X.
Arguments inc {X} x.

(** The destructor [out(inc(x)) :≡ x]. *)
Definition out {X : Type} (z : Copy X) : X := match z with inc x => x end.

Definition inc_out {X : Type} (z : Copy X) : inc (out z) = z
  := match z with inc x => idpath end.

Definition Copy_eqv (X : Type) : Copy X ≃ X
  := mkEqv out inc inc_out (fun _ => idpath).

Definition path_inc_eqv {X : Type} (x x' : X) : (inc x = inc x') ≃ (x = x').
Proof.
  refine (mkEqv (@ap' _ _ out (inc x) (inc x')) (@ap' _ _ inc x x') _ _).
  - intro r.
    enough (G : forall w (r : inc x = w),
               match w return inc x = w -> Type with
               | inc x' => fun r => ap' inc (ap' out r) = r
               end r) by exact (G _ r).
    intros w r'. destruct r'. exact idpath.
  - intro p. change (x = x') in p. destruct p. exact idpath.
Defined.

Definition path_out_eqv {X : Type} (z z' : Copy X) : (out z = out z') ≃ (z = z').
Proof. destruct z as [x], z' as [x']. exact (Eqv_inv (path_inc_eqv x x')). Defined.

(** Example [exa:nnn]: the negated natural numbers [ℕ⁻ :≡ Copy_{-}(ℕ)]. *)
Inductive NNN : Type0 := neg : nat -> NNN.

(** The destructor [-(-n) :≡ n]. *)
Definition unneg (m : NNN) : nat := match m with neg n => n end.

Definition neg_unneg_neg (n : nat) : neg (unneg (neg n)) = neg n := idpath.

Definition NNN_eqv : NNN ≃ nat
  := mkEqv unneg neg (fun m => match m with neg n => idpath end)
           (fun _ => idpath).

(** *** Lists *)

Inductive List (X : Type) : Type :=
| nil : List X
| cons : X -> List X -> List X.
Arguments nil {X}.
Arguments cons {X} x l.

Notation "X ^*" := (List X) (at level 1, format "X ^*") : uf_scope.
Notation ε := nil.

(** The induction principle with its computation rules. *)
Definition List_ind' {X : Type} (T : X^* -> Type) (t_nil : T ε)
  (g : forall x l, T l -> T (cons x l)) : forall l, T l
  := fix f l := match l with
                | ε => t_nil
                | cons x l' => g x l' (f l')
                end.

Definition List_ind'_nil {X} T t g : @List_ind' X T t g ε = t := idpath.
Definition List_ind'_cons {X} T t g (x : X) l
  : List_ind' T t g (cons x l) = g x l (List_ind' T t g l) := idpath.

Definition len {X : Type} : X^* -> nat
  := List_ind' (fun _ => nat) 0%nat (fun _ _ n => S n).

(** Exercise [xca:list-contr]. *)
Definition replicate {X : Type} (c : X) : nat -> X^*
  := fix r n := match n with O => ε | S n' => cons c (r n') end.

Definition len_isEq {X : Type} (H : iscontr X) : isEq (@len X).
Proof.
  refine (iso_to_isEq len (replicate (pr1 H)) _ _).
  - intro l. induction l as [|x l IH].
    + exact idpath.
    + exact (ap011 cons (pr2 H x) IH).
  - intro n. induction n as [|n IH].
    + exact idpath.
    + exact (ap S IH).
Defined.

(** Head and tail. *)
Definition hd {X : Type} (l : X^*) : X ⨿ Unit
  := match l with ε => inr tt | cons x _ => inl x end.

Definition tl {X : Type} (l : X^*) : X^* ⨿ Unit
  := match l with ε => inr tt | cons _ l' => inl l' end.

(** Exercise [xca:reverse]: concatenation, by induction on the first
    argument, and reversal. *)
Definition app {X : Type} (l1 l2 : X^*) : X^*
  := List_ind' (fun _ => X^*) l2 (fun x _ l => cons x l) l1.

Definition rev {X : Type} : X^* -> X^*
  := List_ind' (fun _ => X^*) ε (fun x _ r => app r (cons x ε)).

(** Exercise [xca:concat-assoc]. *)
Definition app_assoc {X : Type} (l1 l2 l3 : X^*)
  : app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
  induction l1 as [|x l1 IH].
  - exact idpath.
  - exact (ap (cons x) IH).
Defined.

(** ** Summary of this formalization

I've formalized §§2.7–2.12 in a new file, [Formalization/IntroUF2.v], which builds on [IntroUF.v] and is added to [_CoqProject]. It compiles cleanly. [Print Assumptions] shows that only the function-extensionality results depend on Coq-HoTT's [Funext] axiom. The other results I checked use no axioms.

How the definitions follow the book
- Book definitions are kept literally: [PathOver] (the type of paths over [p], defined by path induction), [iscontr], [fiber f y := Σ x, (y = f x)], [isEq], and the type of equivalences [X ≃ Y].
- Cases where the book cites the HoTT Book for a proof: these are the converse direction of [lem:weq-iso] and [lem:fiberwise-equiv-from-tot] (Thm 4.7.7). For these I use Coq-HoTT's [isequiv_adjointify] and [isequiv_from_functor_sigma], via conversion lemmas in both directions between the book's [isEq] and Coq-HoTT's [IsEquiv].
- Function extensionality: it is the book's principle that [ptw] is an equivalence, derived from Coq-HoTT's [Funext] axiom. Only the exercises that need it assume it: substitute-away, [(𝟙 → X) ≃ X], and the universal properties of 𝟙, Bool-indexed products and binary sums.
- Sums: Coq-HoTT's Σ-types have definitional η. As a result, AC-in-TT, currying, Σ-associativity, Σ-commutation and Σ-distributivity are equivalences whose round trips hold by definition.
- Binary product: [X × Y] is the Σ-type over a constant family, as in the book. I also show it is equivalent to Coq-HoTT's built-in product type.

Where the formalization differs from the text
- Exercise [xca:cp]: I stated and proved four laws for paths over paths: left unit, right unit, inverse, and double inverse. Where the paths underneath are only propositionally equal, the law is stated by transporting along the corresponding law from §2.5.
- [snd(pair⁼(p,q)) = q]: taken literally, the two sides have different types. I state it together with the [fst] part as [Ψ(pair⁼(p,q)) = (p,q)], where [Ψ] is the inverse map from the proof of [lem:isEq-pair=].
- [lem:isEq-pair-bin=]: [q : y = y'] isn't definitionally a path over [p]. So the map converts [q] with [po_const], and its equivalence is a composite of [tot] (totalization) and the result for general pairs.
- Exercise [xca:binary-sum-id]: I used the encode–decode method rather than the route the book suggests.
- Exercise [xca:sum-equiv-base]: this uses Coq-HoTT's [equiv_functor_sigma_pb], because a direct proof needs half-adjoint coherence, which the book hasn't introduced yet.
- Footnote proof of contract-away: I left this alternative proof out; the main proof is formalized.

Usage note: a file that imports [IntroUF2] should import [HoTT.Basics] first, or Rocq reports a notation-level conflict. *)
