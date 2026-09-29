-- Prove2me | Definitions.Def_Bridges_PosetTheory_TropicalValuationFunctor
-- name    : Bridges_PosetTheory_TropicalValuationFunctor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:58.234766+00:00
-- url     : https://prove2.me/theorems/3cd45083-ea6f-46c4-8e30-42e226f2879a
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_TropicalValuationFunctor
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.TropicalValuationFunctor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/TropicalValuationFunctor.lean by skeleton subtraction
import Mathlib
/-
  # Tropical Valuation Functor:
  # An Order-Preserving Semiring Bridge from Algebraic Coefficients
  # to Tropical Convexity

  ## Domain Bridge: Algebra ↔ Tropical Geometry ↔ Convexity

  The central construction: a valuation-like map from a commutative semiring
  into the tropical semiring (ℕ∞, min, +) that converts algebraic linear
  combinations into tropical convex combinations.

  ## Main Results

  1. `TropicalValuation` — novel structure: a semiring map to (ℕ∞, min, +)
     satisfying v(0)=⊤, v(1)=0, v(ab)=v(a)+v(b), min(v(a),v(b))≤v(a+b).
  2. `padicTropicalValuation` — the p-adic emultiplicity is a tropical valuation.
  3. `tropVal_sum_le_inf` — iterated ultrametric: v(∑ aᵢ) ≥ inf_i v(aᵢ).
  4. `tropVal_lincomb_coord_le` — **Bridge theorem**: coordinatewise valuation
     of ∑ cᵢ xᵢ is bounded below by the tropical combination of v(cᵢ)+v(xᵢⱼ).
  5. `valuation_bridge_tropical_hull_mem` — the coordinatewise valuation image
     of an algebraic linear combination lies in the tropical convex hull.
  6. `TropicalHalfspaceCertificate` — a certificate that a point lies in a
     tropical halfspace, extractable from valuation data.

  ## Falsifiable Conjecture

  `tropVal_surjective_hull_conjecture` — every point in the tropical convex
  hull of v-images of generators is realizable as v of some linear combination.
-/


open Finset BigOperators

noncomputable section

namespace TropicalValuationBridge

/-! ## §1. Tropical Valuation — The Fundamental Structure

A `TropicalValuation` on a commutative semiring R is a map v : R → ℕ∞
satisfying the axioms that make it a homomorphism from (R, +, ·) to the
tropical semiring (ℕ∞, min, +). This generalizes the p-adic valuation
and provides the bridge between algebraic and tropical worlds. -/

/-- A **tropical valuation** on a commutative semiring `R`.
Maps `R` into the extended naturals `ℕ∞ = WithTop ℕ` viewed as
the tropical semiring `(ℕ∞, ⊕ = min, ⊗ = +)`.

The axioms ensure this is a semiring homomorphism to tropical algebra:
- `val_zero`: the zero element maps to the tropical absorbing element ⊤
- `val_one`: the unit maps to the tropical unit 0
- `val_mul`: multiplication becomes tropical multiplication (addition)
- `val_add_le`: addition satisfies the ultrametric inequality

This is the novel bridge structure connecting algebra to tropical geometry. -/
structure TropicalValuation (R : Type*) [CommMonoidWithZero R] [Add R] where
  /-- The valuation map -/
  val : R → ℕ∞
  /-- Zero maps to top (infinity) -/
  val_zero : val 0 = ⊤
  /-- One maps to tropical zero -/
  val_one : val 1 = 0
  /-- Multiplication becomes addition (tropical multiplication) -/
  val_mul : ∀ a b : R, val (a * b) = val a + val b
  /-- Ultrametric inequality: min of valuations ≤ valuation of sum -/
  val_add_le : ∀ a b : R, min (val a) (val b) ≤ val (a + b)

/-! ## §2. The p-Adic Tropical Valuation Instance

The extended multiplicity `emultiplicity p` is a tropical valuation
on any commutative semiring with cancellation. This is the prototypical
example connecting number theory to tropical algebra. -/



/-! ## §3. Iterated Ultrametric Inequality

The ultrametric inequality extends from binary to finite sums:
v(∑ᵢ aᵢ) ≥ inf_i v(aᵢ). This is the key lemma for the bridge theorem. -/

/-
**Iterated ultrametric inequality**: The valuation of a finite sum is
bounded below by the infimum of the individual valuations.
This extends the binary ultrametric property v(a+b) ≥ min(v(a), v(b))
to arbitrary finite sums, which is essential for the bridge theorem.

Proof: by induction on the finset, using the binary ultrametric inequality
and transitivity of min/inf.
-/

/-! ## §4. Valuation of Products (Tropical Functoriality)

The valuation converts products to sums, making it a functor from
multiplicative to additive (tropical) structure. -/

/-
**Valuation of finite products**: v(∏ aᵢ) = ∑ v(aᵢ).
The valuation is a homomorphism from (R, ·) to (ℕ∞, +).
-/

/-
**Valuation of powers**: v(a^n) = n · v(a).
Exponential structure maps to linear tropical scaling.
-/

/-! ## §5. The Bridge Theorem: Coordinatewise Valuation Inequality

**Main result**: For vectors xᵢ ∈ Rⁿ and coefficients cᵢ ∈ R,
the coordinatewise valuation of ∑ cᵢ · xᵢ is bounded below by the
tropical convex combination of the valuation images.

Specifically, for each coordinate j:
  v((∑ᵢ cᵢ · xᵢ)ⱼ) ≥ inf_i (v(cᵢ) + v(xᵢⱼ))

This is the core inequality bridging algebra to tropical convexity. -/

/-- Coordinatewise valuation of a vector. -/
def coordVal {R : Type*} [CommMonoidWithZero R] [Add R]
    (v : TropicalValuation R) {n : ℕ} (x : Fin n → R) : Fin n → ℕ∞ :=
  fun j => v.val (x j)

/-
**Bridge Theorem (Coordinatewise Valuation Inequality)**:
The valuation of each coordinate of a linear combination ∑ cᵢ xᵢ
is bounded below by the tropical combination of the coefficient and
vector valuations.

This is the fundamental bridge: it shows that applying the valuation
to an algebraic linear combination yields a point that is "tropically
dominated" by the tropical combination of the images. In tropical terms,
coordinatewise valuation of ∑ cᵢ xᵢ lies "above" (in the tropical order)
the tropical hull of the valuation images.
-/

/-! ## §6. Tropical Convexity and Hull Membership

We define a simplified tropical convex hull for finite point sets
and show the bridge theorem implies membership. -/

/-- A point `y` in `(ℕ∞)ⁿ` is **tropically dominated** by a finite
family of points `p : Fin k → (Fin n → ℕ∞)` with coefficients
`λ : Fin k → ℕ∞` if for every coordinate j,
  inf_i (λᵢ + pᵢⱼ) ≤ yⱼ.
This is the tropical analogue of "y is a convex combination of pᵢ". -/
def IsTropDominated {n k : ℕ} (y : Fin n → ℕ∞) (p : Fin k → Fin n → ℕ∞)
    (coeffs : Fin k → ℕ∞) : Prop :=
  ∀ j : Fin n, Finset.univ.inf (fun i => coeffs i + p i j) ≤ y j

/-- The **tropical convex hull** of a finite point set: all points
tropically dominated by some choice of tropical coefficients. -/
def tropConvHull {n k : ℕ} (p : Fin k → Fin n → ℕ∞) : Set (Fin n → ℕ∞) :=
  {y | ∃ coeffs : Fin k → ℕ∞, IsTropDominated y p coeffs}

/-
**Bridge: Algebraic combination → Tropical hull membership**.
The coordinatewise valuation of any linear combination ∑ cᵢ xᵢ
lies in the tropical convex hull of the coordinatewise valuations
of the xᵢ.

This is the main bridge theorem: it transports algebraic linear
combinations into tropical convex geometry via the valuation functor.
The tropical coefficients are simply the valuations of the algebraic
coefficients.
-/

/-! ## §7. Tropical Halfspace Certificates

A tropical halfspace is the set of points satisfying a tropical
linear inequality. We show that valuation bounds on coefficients
yield halfspace certificates. -/



/-! ## §8. Monotonicity of Tropical Valuation

The valuation is order-reversing with respect to divisibility:
if a | b then v(a) ≤ v(b). This makes it an order-preserving
map from the divisibility order to the tropical order. -/

/-
**Divisibility implies valuation inequality**: if a | b (and b ≠ 0),
then v(a) ≤ v(b). The valuation is an order-preserving map from
the divisibility poset to (ℕ∞, ≤).
-/

/-
**Valuation strictly increases with prime factors**: if p is such that
v(p) > 0 and a ≠ 0, then v(p * a) > v(a). Each multiplication by a
"non-unit" in the tropical sense strictly increases the valuation.
-/

/-! ## §9. Interaction with Tropical Semiring Certificate

Connect our TropicalValuation to the TropicalSemiringCertificate
structure, showing that the image of a valuation inherits tropical
semiring structure. -/

/-
The tropical semiring structure on `ℕ∞` with min and addition.
-/

/-! ## §10. Falsifiable Conjecture

**Conjecture**: The tropical hull of valuation images equals the set of
valuation images of all possible linear combinations.

This is a strong surjectivity statement: not only does the valuation of
any combination land in the tropical hull, but every point in the tropical
hull is achievable. This is falsifiable because counterexamples can be
found computationally by enumerating small cases. -/


/-! ## §11. Order Structure of Tropical Valuations

The set of tropical valuations on a ring forms a partial order
under pointwise comparison. -/

/-- Pointwise ordering on tropical valuations. -/
instance tropValLE (R : Type*) [CommMonoidWithZero R] [Add R] :
    LE (TropicalValuation R) where
  le v w := ∀ r : R, v.val r ≤ w.val r



end TropicalValuationBridge


