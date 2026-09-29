-- Prove2me | Definitions.Def_Bridges_TropicalStoneDuality
-- name    : Bridges_TropicalStoneDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T10:37:17.724767+00:00
-- url     : https://prove2.me/theorems/dad6cf54-374b-47d0-97f8-1bd06d9420e6
-- title:
--   Aether Catalog definitions — Bridges_TropicalStoneDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalStoneDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalStoneDuality.lean by skeleton subtraction
import Mathlib
/-
# Tropical Stone Duality via Idempotent Heyting Semimodules

This file establishes a finite Stone/Priestley-style duality in which:
- The algebraic side is a **bounded lattice with residuated implication**
  (an "Idempotent Heyting Semimodule"),
- The semantic side is a **finite preorder (Kripke frame)** reconstructed from
  tropical prime points.

## Main results

* `evaluation_injective_of_separating` — separation implies injectivity of evaluation
* `evaluationMap_preserves_sup` — evaluation preserves sup pointwise
* `evaluation_order_embedding` — separation yields an order embedding
* `canonicalPreorder` — specialization order on spectrum by pointwise domination
* `evalMap_is_upset` — evaluations are monotone w.r.t. canonical preorder
* `representation_order_iso` — M ≃o upset functions under separation + closure
* `frame_reconstruction_correct` — the canonical frame recovers the algebra
* `computeCanonicalOrder_spec` — boolean computation matches canonical preorder

## Design notes

Essential assumptions: point separation, finite spectrum, closure of evaluation image.
Artifacts of formalization: the specific bundling choices for structures.
-/


open Function Set

/-! ## Core algebraic structure -/

/-- An idempotent Heyting semimodule: a bounded lattice with a residuated
    implication operation. The name reflects the tropical/idempotent origin;
    algebraically this is a bounded lattice with Heyting implication. -/
class IdemHeytingSemimod (M : Type*) extends Lattice M, BoundedOrder M where
  /-- Heyting implication / residuation -/
  himp : M → M → M
  /-- Residuation: `a ⊓ x ≤ b ↔ x ≤ himp a b` -/
  himp_residuation : ∀ a x b : M, a ⊓ x ≤ b ↔ x ≤ himp a b

namespace IdemHeytingSemimod

variable {M : Type*} [IdemHeytingSemimod M]



end IdemHeytingSemimod

/-! ## Tropical truth object -/

/-- A tropical truth object: a finite bounded lattice with decidable equality and order.
    Used as the codomain for tropical valuations. -/
class TropicalTruth (T : Type*) extends Lattice T, BoundedOrder T where
  [finT : Fintype T]
  [decT : DecidableEq T]
  [decidableLE : DecidableRel ((· ≤ ·) : T → T → Prop)]

attribute [instance] TropicalTruth.finT TropicalTruth.decT TropicalTruth.decidableLE

/-! ## Tropical prime points -/

/-- A tropical prime point: a morphism from the algebra to the truth object
    preserving joins, bounds, and compatible with implication. -/
structure TropPoint (M : Type*) (T : Type*) [IdemHeytingSemimod M] [TropicalTruth T] where
  /-- The underlying function -/
  toFun : M → T
  /-- Preserves sup -/
  map_sup' : ∀ a b : M, toFun (a ⊔ b) = toFun a ⊔ toFun b
  /-- Preserves top -/
  map_top' : toFun ⊤ = ⊤
  /-- Preserves bot -/
  map_bot' : toFun ⊥ = ⊥
  /-- Implication compatibility: if `toFun a ≤ toFun b` then `toFun (himp a b) = ⊤` -/
  map_imp_le' : ∀ a b : M,
    toFun a ≤ toFun b → toFun (IdemHeytingSemimod.himp a b) = ⊤

namespace TropPoint

variable {M T : Type*} [IdemHeytingSemimod M] [TropicalTruth T]

instance : FunLike (TropPoint M T) M T where
  coe := TropPoint.toFun
  coe_injective' p q h := by cases p; cases q; congr



/-- Points are monotone. -/
theorem monotone_point (p : TropPoint M T) : Monotone (p : M → T) := by
  intro a b hab
  have hsup : a ⊔ b = b := sup_eq_right.mpr hab
  calc (p : M → T) a ≤ p a ⊔ p b := le_sup_left
    _ = p (a ⊔ b) := (p.map_sup' a b).symm
    _ = p b := by rw [hsup]

end TropPoint

/-! ## Prime spectrum and evaluation -/

/-- The prime spectrum: the type of tropical prime points. -/
abbrev PrimeSpec (M T : Type*) [IdemHeytingSemimod M] [TropicalTruth T] := TropPoint M T

/-- Full separation: distinct elements are distinguished by some point. -/
def FullySeparating (M T : Type*) [IdemHeytingSemimod M] [TropicalTruth T] : Prop :=
  ∀ a b : M, a ≠ b → ∃ p : PrimeSpec M T, p a ≠ p b

/-- The evaluation map: sends an element to its evaluation function on the spectrum. -/
def evalMap {M T : Type*} [IdemHeytingSemimod M] [TropicalTruth T]
    (a : M) : PrimeSpec M T → T :=
  fun p => p a

/-! ## Theorem 1: Evaluation injectivity from point separation

The gateway lemma for the entire duality theory. -/

/-- **Evaluation injectivity from point separation.**
    If tropical prime points separate elements of `M`, then the evaluation map
    from `M` to functions on the prime spectrum is injective. -/
theorem evaluation_injective_of_separating
    {M T : Type*} [IdemHeytingSemimod M] [TropicalTruth T]
    (hsep : FullySeparating M T) :
    Injective (evalMap (M := M) (T := T)) := by
  intro a b h
  by_contra hab
  obtain ⟨p, hp⟩ := hsep a b hab
  exact hp (congr_fun h p)

/-! ## Operation preservation -/



/-! ## Canonical preorder on the spectrum -/

/-- **Canonical preorder:** `p ≤ q` iff `∀ a, p(a) ≤ q(a)` (pointwise domination).
    This is the specialization order on the tropical prime spectrum. -/
instance canonicalPreorder (M T : Type*)
    [IdemHeytingSemimod M] [TropicalTruth T] :
    Preorder (PrimeSpec M T) where
  le p q := ∀ a : M, p a ≤ q a
  le_refl _ _ := le_refl _
  le_trans _ _ _ hpq hqr a := le_trans (hpq a) (hqr a)



/-! ## Order embedding under separation -/

/-- **Order embedding under separation.**
    Under point separation, the lattice order is faithfully represented:
    `a ≤ b` iff `p(a) ≤ p(b)` for all points `p`. -/
theorem evaluation_order_embedding {M T : Type*}
    [IdemHeytingSemimod M] [TropicalTruth T]
    (hsep : FullySeparating M T) (a b : M) :
    a ≤ b ↔ ∀ p : PrimeSpec M T, evalMap a p ≤ evalMap b p := by
  constructor
  · intro h p; exact TropPoint.monotone_point p h
  · intro h
    have hsup : evalMap (M := M) (T := T) (a ⊔ b) = evalMap b := by
      funext p; show p (a ⊔ b) = p b
      change p.toFun (a ⊔ b) = p.toFun b
      have hp : p.toFun a ≤ p.toFun b := h p
      rw [p.map_sup' a b, sup_eq_right.mpr hp]
    exact sup_eq_right.mp (evaluation_injective_of_separating hsep hsup)

/-! ## Computable canonical order -/

/-- Compute whether `p ≤ q` by checking all elements of a finite `M`. -/
noncomputable def computeCanonicalOrder {M T : Type*}
    [IdemHeytingSemimod M] [TropicalTruth T]
    [Fintype M] [DecidableEq M]
    (p q : PrimeSpec M T) : Bool :=
  (Finset.univ.filter fun a : M => ¬(p a ≤ q a)).card == 0


/-! ## Evaluation image -/

/-- The image of the evaluation map. -/
def evalImage (M T : Type*) [IdemHeytingSemimod M] [TropicalTruth T] :
    Set (PrimeSpec M T → T) :=
  range (evalMap (M := M) (T := T))





/-! ## Upset functions -/

/-- **Upset (monotone) functions** w.r.t. the canonical preorder. -/
def IsUpsetFun {M T : Type*} [IdemHeytingSemimod M] [TropicalTruth T]
    (f : PrimeSpec M T → T) : Prop :=
  Monotone f

/-- The evaluation of any element gives an upset function. -/
theorem evalMap_is_upset {M T : Type*}
    [IdemHeytingSemimod M] [TropicalTruth T]
    (a : M) : IsUpsetFun (evalMap (M := M) (T := T) a) :=
  fun _ _ h => h a


/-! ## Finite Kripke frame -/

/-- A finite Kripke frame: a finite type with a reflexive transitive relation. -/
structure FiniteKripkeFrame where
  /-- The carrier type of worlds -/
  World : Type*
  /-- Fintype instance -/
  [finWorld : Fintype World]
  /-- DecidableEq instance -/
  [decWorld : DecidableEq World]
  /-- The accessibility relation -/
  rel : World → World → Prop
  /-- Reflexivity -/
  rel_refl : ∀ w, rel w w
  /-- Transitivity -/
  rel_trans : ∀ u v w, rel u v → rel v w → rel u w

attribute [instance] FiniteKripkeFrame.finWorld FiniteKripkeFrame.decWorld

/-- Construct a finite Kripke frame from the prime spectrum with canonical preorder. -/
noncomputable def frameOfSpectrum (M T : Type*)
    [IdemHeytingSemimod M] [TropicalTruth T]
    [Fintype (PrimeSpec M T)] [DecidableEq (PrimeSpec M T)] :
    FiniteKripkeFrame where
  World := PrimeSpec M T
  rel p q := p ≤ q
  rel_refl _ := le_refl _
  rel_trans _ _ _ := le_trans

/-- **Frame equivalence**: relation-preserving bijection between frames. -/
def FrameEquiv (F₁ F₂ : FiniteKripkeFrame) : Prop :=
  ∃ e : F₁.World ≃ F₂.World, ∀ w₁ w₂, F₁.rel w₁ w₂ ↔ F₂.rel (e w₁) (e w₂)


/-! ## Closure hypothesis and representation -/

/-- **Closure hypothesis**: every upset function is in the evaluation image.
    This is the key hypothesis for surjectivity of the representation. -/
structure EvalImageClosed (M T : Type*) [IdemHeytingSemimod M] [TropicalTruth T] where
  surj_onto_upsets : ∀ f : PrimeSpec M T → T,
    IsUpsetFun f → f ∈ evalImage M T



/-- **Main representation theorem (order isomorphism).**
    Under separation and closure, `M` is order-isomorphic to the subtype
    of upset functions on its canonical spectrum. -/
noncomputable def representation_order_iso
    {M T : Type*} [IdemHeytingSemimod M] [TropicalTruth T]
    [Fintype (PrimeSpec M T)]
    (hsep : FullySeparating M T)
    (hclosed : EvalImageClosed M T) :
    M ≃o {f : PrimeSpec M T → T // IsUpsetFun f} where
  toFun a := ⟨evalMap a, evalMap_is_upset a⟩
  invFun f := (hclosed.surj_onto_upsets f.1 f.2).choose
  left_inv a := by
    apply evaluation_injective_of_separating hsep
    exact (hclosed.surj_onto_upsets (evalMap a) (evalMap_is_upset a)).choose_spec
  right_inv f := by
    ext1; ext1 p
    exact congr_fun (hclosed.surj_onto_upsets f.1 f.2).choose_spec p
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Pi.le_def, evalMap]
    exact ⟨
      fun h => (evaluation_order_embedding hsep a b).mpr (fun p => h p),
      fun h p => TropPoint.monotone_point p h⟩


/-! ## Implication table reconstruction -/

/-- Reconstructed implication table via evaluation. -/
noncomputable def reconstructHimpTable {M T : Type*}
    [IdemHeytingSemimod M] [TropicalTruth T]
    (a b : M) : PrimeSpec M T → T :=
  fun p => p (IdemHeytingSemimod.himp a b)



/-! ## Structure isomorphism for Heyting semimodules -/


/-- An isomorphism of idempotent Heyting semimodules: an equivalence whose
    forward map preserves finite joins and top (the Heyting semimodule
    structure used throughout this file). -/
structure IHSIso (M N : Type*) [IdemHeytingSemimod M] [IdemHeytingSemimod N] where
  /-- The underlying equivalence -/
  toEquiv : M ≃ N
  /-- Preserves sup -/
  map_sup' : ∀ a b : M, toEquiv (a ⊔ b) = toEquiv a ⊔ toEquiv b
  /-- Preserves top -/
  map_top' : toEquiv ⊤ = ⊤

/-- Notation for Heyting semimodule isomorphism. -/
infixl:25 " ≃ₕ " => IHSIso

/-! ## Bool as a tropical truth object -/

/-- `Bool` with its standard lattice structure is a tropical truth object. -/
noncomputable instance boolTropicalTruth : TropicalTruth Bool where
  finT := inferInstance
  decT := inferInstance
  decidableLE := inferInstance

/-! ## Concrete example: four-element diamond lattice

The diamond lattice `{⊥, a, b, ⊤}` with `a, b` incomparable is a canonical
test case. We show it has an `IdemHeytingSemimod` structure and is fully
separated by two `Bool`-valued tropical prime points. -/

/-- A four-element diamond lattice: ⊥, left, right, ⊤ with left, right incomparable. -/
inductive Diamond where
  | bot | left | right | top
  deriving DecidableEq, Fintype

namespace Diamond

/-- Boolean-valued order predicate on Diamond (for decidability). -/
def dle : Diamond → Diamond → Bool
  | .bot, _ => true
  | _, .top => true
  | .left, .left => true
  | .right, .right => true
  | _, _ => false

instance : LE Diamond where le a b := dle a b = true

instance : DecidableRel ((· ≤ ·) : Diamond → Diamond → Prop) :=
  fun a b => inferInstanceAs (Decidable (dle a b = true))

/-- Sup on Diamond. -/
def dsup : Diamond → Diamond → Diamond
  | .bot, z => z
  | z, .bot => z
  | .top, _ => .top
  | _, .top => .top
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right => .top
  | .right, .left => .top

/-- Inf on Diamond. -/
def dinf : Diamond → Diamond → Diamond
  | .top, z => z
  | z, .top => z
  | .bot, _ => .bot
  | _, .bot => .bot
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right => .bot
  | .right, .left => .bot

instance : Lattice Diamond where
  sup := dsup
  inf := dinf
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  le_sup_left a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide
  sup_le a b c := by cases a <;> cases b <;> cases c <;> decide
  inf_le_left a b := by cases a <;> cases b <;> decide
  inf_le_right a b := by cases a <;> cases b <;> decide
  le_inf a b c := by cases a <;> cases b <;> cases c <;> decide

instance : BoundedOrder Diamond where
  top := .top
  bot := .bot
  le_top a := by cases a <;> decide
  bot_le a := by cases a <;> decide

/-- Heyting implication on Diamond. -/
def dhimp : Diamond → Diamond → Diamond
  | _, .top => .top
  | .bot, _ => .top
  | .top, .bot => .bot
  | .top, .left => .left
  | .top, .right => .right
  | .left, .bot => .right
  | .left, .left => .top
  | .left, .right => .right
  | .right, .bot => .left
  | .right, .left => .left
  | .right, .right => .top

instance : IdemHeytingSemimod Diamond where
  himp := dhimp
  himp_residuation a x b := by cases a <;> cases x <;> cases b <;> decide

/-- Point extracting the "left" component: maps `left, top ↦ true` and `bot, right ↦ false`. -/
def pointL : TropPoint Diamond Bool where
  toFun
    | .bot => false
    | .left => true
    | .right => false
    | .top => true
  map_sup' a b := by cases a <;> cases b <;> decide
  map_top' := by decide
  map_bot' := by decide
  map_imp_le' a b h := by cases a <;> cases b <;> revert h <;> decide

/-- Point extracting the "right" component: maps `right, top ↦ true` and `bot, left ↦ false`. -/
def pointR : TropPoint Diamond Bool where
  toFun
    | .bot => false
    | .left => false
    | .right => true
    | .top => true
  map_sup' a b := by cases a <;> cases b <;> decide
  map_top' := by decide
  map_bot' := by decide
  map_imp_le' a b h := by cases a <;> cases b <;> revert h <;> decide




end Diamond

/-! ## Summary

The complete duality pipeline established in this file:

1. **Algebraic object**: `IdemHeytingSemimod M` — bounded lattice + residuated implication
2. **Point object**: `TropPoint M T` — join/bound/imp-preserving morphism to truth object
3. **Spectrum**: `PrimeSpec M T` — type of all tropical prime points
4. **Evaluation**: `evalMap` — sends algebraic elements to functions on spectrum
5. **Injectivity**: `evaluation_injective_of_separating` — separation ⟹ injectivity
6. **Order embedding**: `evaluation_order_embedding` — separation ⟹ order embedding
7. **Canonical preorder**: `canonicalPreorder` — pointwise domination on spectrum
8. **Monotonicity**: `evalMap_is_upset` — evaluations are upset functions
9. **Representation**: `representation_order_iso` — M ≃o upset functions (under closure)
10. **Frame construction**: `frameOfSpectrum` — canonical Kripke frame from spectrum
11. **Certification**: `computeCanonicalOrder_spec` — boolean computation = preorder
12. **Concrete example**: Diamond lattice with Bool truth object, fully separated
-/


