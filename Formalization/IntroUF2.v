(** * Formalization of Sections 2.7 - 2.12 of [intro-uf.tex]

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

From HoTT Require Import Basics Types.Sigma Types.Equiv Types.Bool
  Cubical.DPath Spaces.List.Core.
From SymmetryMirror Require Import IntroUF.

Local Open Scope uf_scope.

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

(** Example [exa:nnn]: the negated natural numbers [ℕ⁻ :≡ Copy_{-}(ℕ)]. *)
Inductive NNN : Type0 := neg : ℕ -> NNN.

(** The destructor [-(-n) :≡ n]. *)
Definition unneg (m : NNN) : ℕ := match m with neg n => n end.

Definition neg_unneg_neg (n : ℕ) : neg (unneg (neg n)) = neg n := refl.

Definition NNN_eqv : NNN ≃ ℕ
  := mkEqv unneg neg (fun m => match m with neg n => refl end)
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
