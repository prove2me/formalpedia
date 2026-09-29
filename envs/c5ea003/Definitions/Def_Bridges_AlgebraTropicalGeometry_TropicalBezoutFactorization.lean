-- Prove2me | Definitions.Def_Bridges_AlgebraTropicalGeometry_TropicalBezoutFactorization
-- name    : Bridges_AlgebraTropicalGeometry_TropicalBezoutFactorization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:08:11.16986+00:00
-- url     : https://prove2.me/theorems/281132a9-827c-490c-b0f4-3abc75cdeacf
-- title:
--   Aether Catalog definitions — Bridges_AlgebraTropicalGeometry_TropicalBezoutFactorization
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlgebraTropicalGeometry.TropicalBezoutFactorization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlgebraTropicalGeometry/TropicalBezoutFactorization.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Bézout: factorization of tropical hypersurfaces and Newton polytopes

This file *extends* `Bridges.AlgebraTropicalGeometry.TropicalValuationLimitBridge`.  That file
established the bridge between a non-Archimedean valuation and tropical geometry, proving:

* `TropicalValuationBridge.kapranov_easy_direction` — the easy direction of the Fundamental
  Theorem of Tropical Geometry (tropicalization ⊆ corner locus), and
* `TropicalValuationBridge.TropPoly.eval_mul` — min-plus multiplicativity
  `eval (P ⊙ Q) = eval P + eval Q`, the *engine* of tropical Bézout.

To keep this file self-contained (and to let it be checked in isolation) we re-state the two
small pieces of vocabulary from that bridge file — the corner-locus predicate
`AttainedAtLeastTwice` and the `TropPoly` structure with its tropical product `TropPoly.mul` —
and then prove the genuinely new **tropical Bézout / factorization** theorems on top of them.

## Main results

* `TropicalBezout.attainedTwice_smul` — **scale invariance of the corner locus**
  (the "valuation → ∞" limit).  Rescaling all weights by a positive constant `t` (as happens
  when the valuation `v` is replaced by `t · v`) does not change the corner locus.  This is the
  precise sense in which the tropical variety is the scale-invariant *limit* of the family of
  amoebas.  It complements `kapranov_easy_direction`, which produces a corner from a single `v`.

* `TropicalBezout.tropRoot_mul_iff` — **the tropical hypersurface of a product is the union of
  the hypersurfaces.**  A point is a tropical root of `P ⊙ Q` iff it is a tropical root of `P` or
  of `Q`.  Combined with `eval_mul` (degrees add), this is the combinatorial core of the tropical
  Bézout theorem: a degree-`d`·degree-`e` intersection decomposes into the right count of pieces.

* `TropicalBezout.tropRootSet_mul` — the set-level restatement `V(P ⊙ Q) = V(P) ∪ V(Q)`.

* `TropicalBezout.range_exp_mul` — **Newton polytopes add (Minkowski sum).**  The exponent
  support of `P ⊙ Q` is the Minkowski sum of the supports of `P` and `Q`.  This is the
  polytope-level shadow of degree additivity underlying Bézout's degree count.

* A boundary case (`tropRoot_mul_subsingleton_right`): multiplying by a single tropical monomial
  adds no roots.
-/

open Finset
open scoped Pointwise

namespace TropicalBezout

/-! ## §0. Vocabulary inherited from the bridge file (re-stated for self-containment) -/

/-- A weight function `w : ι → α` **attains its minimum at least twice** when there are two
distinct indices that are both global minima.  Geometrically this is the *corner locus*
(tropical hypersurface) condition.  Mirrors
`TropicalValuationBridge.AttainedAtLeastTwice`. -/
def AttainedAtLeastTwice {ι α : Type*} [LinearOrder α] (w : ι → α) : Prop :=
  ∃ i j, i ≠ j ∧ (∀ k, w i ≤ w k) ∧ (∀ k, w j ≤ w k)

/-- A tropical polynomial in `n` variables: a finite family of monomials, each a real coefficient
together with a (real) exponent vector.  Mirrors `TropicalValuationBridge.TropPoly`. -/
structure TropPoly (ι : Type*) (n : ℕ) where
  /-- The tropical coefficient of each monomial. -/
  coeff : ι → ℝ
  /-- The exponent vector of each monomial. -/
  exp : ι → (Fin n → ℝ)

/-- The value of the `i`-th monomial at the tropical point `x`: `coeff i + ⟨exp i, x⟩`. -/
def TropPoly.termVal {ι : Type*} {n : ℕ} (P : TropPoly ι n) (x : Fin n → ℝ) (i : ι) : ℝ :=
  P.coeff i + ∑ k, P.exp i k * x k

/-- Tropical (min-plus) product of two tropical polynomials: monomials multiply by adding
coefficients and exponents.  Mirrors `TropicalValuationBridge.TropPoly.mul`. -/
def TropPoly.mul {ι κ : Type*} {n : ℕ} (P : TropPoly ι n) (Q : TropPoly κ n) :
    TropPoly (ι × κ) n where
  coeff := fun p => P.coeff p.1 + Q.coeff p.2
  exp := fun p => P.exp p.1 + Q.exp p.2

/-
!-- A single index can never witness `i ≠ j`. -- !--
A one-monomial tropical polynomial has empty corner locus.  Mirrors
`TropicalValuationBridge.attainedTwice_subsingleton`.
-/

/-! ## §1. Scale invariance of the corner locus — the "valuation → ∞" limit -/

/-
!-- Multiplying every weight by a fixed `t > 0` is an order isomorphism on `ℝ`, so
`t * w i ≤ t * w k ↔ w i ≤ w k`; the witnessing indices of the corner are therefore unchanged. -- !--

**Scale invariance (the limiting tropical shape).**  Classically one studies the rescaled
valuations `v_t = t · v` as `t → ∞`.  The corner-locus predicate `AttainedAtLeastTwice` is
invariant under such a positive rescaling, so the tropical variety is genuinely the
scale-independent limit of the family.
-/

/-! ## §2. The general combinatorial lemma: minimizers of a separated sum -/

/-
!-- A pair `(i,k)` minimizes `a i + b k` iff `i` minimizes `a` and `k` minimizes `b`; the
minimizing set is the product of the two minimizing sets, which has ≥ 2 elements iff one factor
does.  Minimizers of `a` and `b` exist by finiteness. -- !--

**Separated-sum corner lemma.**  For a function of the form `(i,k) ↦ a i + b k` on a product of
finite nonempty types, the corner-locus condition holds iff it holds for `a` or for `b`.  This is
the engine behind the tropical factorization theorem below.
-/

/-! ## §3. Tropical hypersurface of a product = union of hypersurfaces -/

/-- A point `x` is a **tropical root** of `P` when the minimum defining `P`'s tropical evaluation
is attained by at least two monomials, i.e. `x` lies on the corner locus / tropical hypersurface
`V(P)`. -/
def IsTropRoot {ι : Type*} {n : ℕ} (P : TropPoly ι n) (x : Fin n → ℝ) : Prop :=
  AttainedAtLeastTwice (P.termVal x)


/-
!-- Rewrite `termVal (P ⊙ Q)` as the separated sum via `termVal_mul`, then apply
`attainedTwice_add_iff`. -- !--

**Tropical Bézout / factorization (headline).**  A point is a tropical root of the product
`P ⊙ Q` iff it is a tropical root of `P` or of `Q`: the tropical hypersurface of a product is the
union of the hypersurfaces.  This is the combinatorial heart of tropical Bézout, complementing the
degree-additivity engine `TropPoly.eval_mul` from the bridge file.
-/

/-
**Set-level restatement: `V(P ⊙ Q) = V(P) ∪ V(Q)`.**  The tropical zero set of a product is the
union of the tropical zero sets of the factors.
-/

/-! ## §4. Newton polytopes add: the Minkowski-sum law -/

/-
!-- `(P ⊙ Q).exp (i,k) = P.exp i + Q.exp k`, so the range over all pairs is exactly the
pointwise (Minkowski) sum of the two ranges. -- !--

**Newton polytopes add (Minkowski sum).**  The exponent support of the tropical product is the
Minkowski sum of the exponent supports of the factors.  This is the polytope-level expression of
degree additivity (`eval_mul`) and is what makes the Bézout degree count `deg = d · e` work.
-/

/-! ## §5. Boundary case of the headline theorem -/

/-
!-- If `κ` has at most one monomial, `Q` can never contribute a corner, so the union collapses to
`V(P)`; this follows from `tropRoot_mul_iff` together with `attainedTwice_subsingleton`. -- !--

**Boundary case.**  When `Q` is a single tropical monomial (`κ` a subsingleton), it has no corner
locus, so the product's hypersurface is just that of `P`: multiplying by a monomial adds no roots.
-/

end TropicalBezout


