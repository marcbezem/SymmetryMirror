(** * Bridges between the book's notions and Coq-HoTT

    ** Summary of this formalization

    This file collects, in one place, the conversions between the
    notions defined in [IntroUF.v], [IntroUF2.v] and [IntroUF3.v] and
    their counterparts in the Coq-HoTT library, so that library results
    can be reused for the book's notions.  It compiles; [Print
    Assumptions] shows that Coq-HoTT's [Funext] is used only by the
    equivalences between proposition-valued notions (to show that the
    notions involved are propositions), by [Equiv_Eqv_eqv] and by
    [ptw_inv_is_path_forall]; all other bridges use no axioms.

    - Notions defined from library notions (via
      [Definition book_name := library_name]) agree by definition: [symm],
      [trp], [ptw], [PathOver], [apd], [apap], [comp], [fst], [snd],
      [tot], [mul], [fact]; for addition, [add n m ≡ nat_add m n].
    - Path composition: [q ⋅ p = p @ q] ([trans_is_concat] from
      [IntroUF.v]), and [add n m = nat_add n m].
    - Function extensionality: [ptw⁻¹ = path_forall].
    - Fibers: [fiber f y ≃ hfiber f y] (the conventions [y = f x] and
      [f x = y] differ by path inversion).
    - Contractibility: [isContr X ≃ Contr X].
    - Propositions, sets, groupoids and n-types: [isProp P ≃ IsHProp P],
      [isSet X ≃ IsHSet X], [isGrpd X ≃ IsTrunc 1 X] and
      [is_ntype n X ≃ IsTrunc (tr_nat n) X].
    - Equivalences: [isEquiv f ≃ IsEquiv f], and [(X ≃ Y) ≃ (X <~> Y)]
      with [Equiv_of_Eqv] as the map from the book's equivalences.
    - Binary products: [X × Y ≃ X * Y] ([binprod_prod] from [IntroUF2.v]),
      and identifications of pairs in [X × Y] correspond to
      [path_prod].

    The book's predicates are not registered as type classes, so library
    automation (instance search for [IsHProp], [IsTrunc], [IsEquiv]) is
    reached by applying these conversions explicitly.

    ** Conventions

    As in [IntroUF.v], [IntroUF2.v] and [IntroUF3.v]. *)

From HoTT Require Import Basics Types.Sigma Types.Prod Types.Equiv
  Types.Forall Types.Paths Cubical.DPath Spaces.Nat.Core.
From SymmetryMirror Require Import IntroUF IntroUF2 IntroUF3.

Local Open Scope uf_scope.

(** ** Notions that agree by definition *)

Definition symm_is_inverse {X : Type} {a b : X} (p : a = b)
  : p⁻¹ = p^ := refl.

Definition trp_is_transport {X : Type} (T : X -> Type) {a b : X} (e : a = b)
  : trp T e = transport T e := refl.

Definition ptw_is_apD10 {X : Type} {Y : X -> Type} {f g : forall x, Y x}
  (p : f = g) : ptw p = apD10 p := refl.

Definition PathOver_is_DPath {X : Type} (Y : X -> Type) {a a' : X}
  (p : a = a') (y : Y a) (y' : Y a')
  : PathOver Y p y y' = DPath Y p y y' := refl.

Definition apd_is_apD {X : Type} {Y : X -> Type} (f : forall x, Y x)
  {x x' : X} (p : x = x') : apd f p = apD f p := refl.

Definition apap_is_ap011D {X Z : Type} {Y : X -> Type}
  (g : forall x, Y x -> Z) {x x' : X} {y : Y x} {y' : Y x'}
  (p : x = x') (q : PathOver Y p y y')
  : apap g p q = ap011D g p q := refl.

Definition comp_is_compose {X Y Z : Type} (g : Y -> Z) (f : X -> Y)
  : g ∘ f = (g o f)%function := refl.

Definition fst_is_pr1 {X : Type} {Y : X -> Type} (z : {x : X & Y x})
  : fst z = pr1 z := refl.

Definition snd_is_pr2 {X : Type} {Y : X -> Type} (z : {x : X & Y x})
  : snd z = pr2 z := refl.

Definition tot_is_functor_sigma {X : Type} {Y Z : X -> Type}
  (f : forall x, Y x -> Z x) : tot f = functor_sigma idmap f := refl.

(** ** Arithmetic *)

Definition add_is_nat_add_swap (n m : ℕ) : add n m = nat_add m n := refl.

Definition add_is_nat_add (n m : ℕ) : add n m = nat_add n m
  := nat_add_comm m n.

Definition mul_is_nat_mul (m n : ℕ) : mul m n = nat_mul m n := refl.

(** ** Path composition

    [trans_is_concat : q ⋅ p = p @ q] is in [IntroUF.v]. *)

Definition trans_is_concat' {X : Type} {a b c : X} (p : a = b) (q : b = c)
  : trans p q = concat p q
  := trans_is_concat p q.

(** ** Function extensionality: [ptw⁻¹] is [path_forall]. *)

Definition ptw_inv_is_path_forall `{Funext} {X : Type} {Y : X -> Type}
  {f g : forall x, Y x} (h : forall x, f x = g x)
  : ptw_inv h = path_forall f g h
  := ap (eqinv (funext f g)) (eisretr apD10 h)^
     @ eqinv_l (funext f g) (path_forall f g h).

(** ** Equivalences between propositions *)

Definition Eqv_of_props {P Q : Type} (hP : isProp P) (hQ : isProp Q)
  (f : P -> Q) (g : Q -> P) : P ≃ Q
  := mkEqv f g (fun p => hP _ _) (fun q => hQ _ _).

(** ** Fibers: [y = f x] versus [f x = y] *)

Definition fiber_hfiber {X Y : Type} (f : X -> Y) (y : Y)
  : fiber f y ≃ hfiber f y
  := mkEqv (fun w : fiber f y => (fst w; (snd w)^) : hfiber f y)
           (fun w : hfiber f y => (pr1 w; (pr2 w)^) : fiber f y)
           (fun w => ap (fun r => (fst w; r) : fiber f y) (inv_V (snd w)))
           (fun w => ap (fun r => (pr1 w; r) : hfiber f y) (inv_V (pr2 w))).

(** ** Contractibility *)

Definition Contr_of_isContr {X : Type} (h : isContr X) : Contr X
  := Build_Contr X (fst h) (snd h).

Definition isContr_of_Contr {X : Type} `{Contr X} : isContr X
  := (center X; contr).

Definition isContr_Contr_eqv `{Funext} (X : Type) : isContr X ≃ Contr X
  := Eqv_of_props (isContr_isProp X) (IsHProp_isProp (P := Contr X))
       Contr_of_isContr (fun C => @isContr_of_Contr X C).

(** ** Propositions, sets, groupoids and n-types *)

Definition isProp_eqv `{Funext} (P : Type) : isProp P ≃ IsHProp P
  := Eqv_of_props (isProp_isProp P) (IsHProp_isProp (P := IsHProp P))
       isProp_IsHProp (fun h => @IsHProp_isProp P h).

Definition is_ntype_eqv `{Funext} (n : ℕ) (X : Type)
  : is_ntype n X ≃ IsTrunc (tr_nat n) X
  := Eqv_of_props (ntype_isProp n X)
       (IsHProp_isProp (P := IsTrunc (tr_nat n) X))
       (ntype_IsTrunc n) (IsTrunc_ntype n).

Definition isSet_IsHSet {X : Type} : isSet X -> IsHSet X := ntype_IsTrunc 0.
Definition IsHSet_isSet {X : Type} : IsHSet X -> isSet X := IsTrunc_ntype 0.

Definition isSet_eqv `{Funext} (X : Type) : isSet X ≃ IsHSet X
  := is_ntype_eqv 0 X.

Definition isGrpd_IsTrunc {X : Type} : isGrpd X -> IsTrunc 1 X
  := ntype_IsTrunc 1.
Definition IsTrunc_isGrpd {X : Type} : IsTrunc 1 X -> isGrpd X
  := IsTrunc_ntype 1.

Definition isGrpd_eqv `{Funext} (X : Type) : isGrpd X ≃ IsTrunc 1 X
  := is_ntype_eqv 1 X.

(** ** Equivalences *)

Definition isEquiv_IsEquiv_eqv `{Funext} {X Y : Type} (f : X -> Y)
  : isEquiv f ≃ IsEquiv f
  := Eqv_of_props (isEquiv_isProp f) (IsHProp_isProp (P := IsEquiv f))
       IsEquiv_of_isEquiv (fun e => @isEquiv_of_IsEquiv X Y f e).

Definition Equiv_of_Eqv {X Y : Type} (e : X ≃ Y) : X <~> Y
  := Build_Equiv X Y (fst e) (IsEquiv_of_isEquiv (snd e)).

Definition Equiv_of_Eqv_fun {X Y : Type} (e : X ≃ Y)
  : equiv_fun (Equiv_of_Eqv e) = fst e := refl.

Definition Equiv_Eqv_eqv `{Funext} (X Y : Type) : (X <~> Y) ≃ (X ≃ Y)
  := (Eqv_of_Equiv; Eqv_of_Equiv_isEquiv X Y).

(** ** Binary products

    [binprod_prod : (X × Y) ≃ (X * Y)] is in [IntroUF2.v].  Identifications
    of pairs in [X × Y] correspond to the library's [path_prod]. *)

Definition binprod_paths_eqv {X Y : Type} (x x' : X) (y y' : Y)
  : ((x; y) = (x'; y') :> X × Y) ≃ ((x, y) = (x', y') :> X * Y)
  := Eqv_comp (Eqv_comp (Eqv_inv (path_prod_eqv x x' y y'))
                        (binprod_prod (x = x') (y = y')))
       (Eqv_of_Equiv (equiv_path_prod (x, y) (x', y'))).
