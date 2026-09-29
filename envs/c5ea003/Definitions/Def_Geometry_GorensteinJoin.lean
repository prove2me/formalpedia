-- Prove2me | Definitions.Def_Geometry_GorensteinJoin
-- name    : Geometry_GorensteinJoin
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:01.914366+00:00
-- url     : https://prove2.me/theorems/20d9d531-56bf-4d3c-a0a0-6eeefc7a7ad9
-- title:
--   Aether Catalog definitions — Geometry_GorensteinJoin
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.GorensteinJoin`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/GorensteinJoin.lean by skeleton subtraction
import Mathlib

/-!
# The Join of Gorenstein Polytopes IS Gorenstein

**Research mission.** "Join of Gorenstein Polytopes is Not Necessarily Gorenstein."

**Headline finding (refutation of the title).** The proposed direction is *false*: the
join of two Gorenstein lattice polytopes is *always* Gorenstein. We prove this rigorously
at the level of the Ehrhart `h*`-polynomial (`δ`-polynomial), which is the standard and
faithful invariant governing the Gorenstein property.

## Mathematical background

For a lattice polytope `P` of dimension `d`, the Ehrhart series can be written
`∑_{t ≥ 0} L_P(t) z^t = h*_P(z) / (1 - z)^{d+1}`, where the numerator `h*_P` (the
`h*`-polynomial, a.k.a. `δ`-polynomial) has nonnegative integer coefficients (Stanley)
and constant term `h*_0 = 1`.

* **Gorenstein criterion (Stanley/Hibi).** `P` is Gorenstein iff its `h*`-vector is
  *symmetric* (palindromic): `h*_i = h*_{s - i}` for all `i`, where `s = deg h*_P`.
  Equivalently `h*_P.reverse = h*_P`.

* **Join multiplicativity (classical Ehrhart theory).** For the join
  `P ∗ Q ⊆ ℝ^{m+n+1} = conv(P × {0} × {0} ∪ {0} × Q × {1})` one has
  `h*_{P ∗ Q}(z) = h*_P(z) · h*_Q(z)` and `dim(P ∗ Q) = dim P + dim Q + 1`.
  (Codegrees add; degrees of `h*` add.)

We therefore model a Gorenstein polytope by its `h*`-data: a polynomial over `ℤ` with
constant term `1`, nonnegative coefficients, and palindromic (`reverse = self`). The join
is modeled by polynomial multiplication. The theorem `GorensteinHStar.join` shows this
operation lands back in the Gorenstein class.

-- !-- Lab Notes -- !--
HYPOTHESIS (from the mission title): ∃ Gorenstein P, Q with P ∗ Q NOT Gorenstein.
EXPERIMENT 1: Compute the `h*`-criterion. Gorenstein ⟺ palindromic `h*`. Join ⟺ product
  of `h*`. So the title reduces to: "∃ palindromic p, q with p·q not palindromic."
EXPERIMENT 2: Reflect a product. If `t^d p(1/t) = p` and `t^e q(1/t) = q`, then
  `t^{d+e}(pq)(1/t) = (t^d p(1/t))(t^e q(1/t)) = p q`. So the product is ALWAYS palindromic.
OUTCOME: The hypothesis is FALSE. The join of Gorenstein polytopes is always Gorenstein.
  Formally this is `Polynomial.reverse_mul_of_domain` (reverse is multiplicative over an
  integral domain) applied to two symmetric factors.
INSIGHT / FAILURE ANALYSIS: The intuition behind the title is real but misattributed — it
  is the *free sum* `P ⊕ Q`, NOT the join, whose `h*`-polynomial fails to be multiplicative
  and whose Gorenstein property can break. We record that distinction in
  `freeSum_concat_not_symmetric` (a concrete non-palindromic concatenation) and in
  FUTURE_DIRECTIONS.md.
-/

open Polynomial

namespace GorensteinJoin

/-- The Ehrhart `h*`-data of a Gorenstein lattice polytope: a polynomial over `ℤ` with
constant term `1` (always true for lattice polytopes), nonnegative coefficients (Stanley's
nonnegativity theorem), and a palindromic / symmetric coefficient vector
(`reverse = self`), which is exactly the Gorenstein criterion of Stanley and Hibi. -/
structure GorensteinHStar where
  /-- The `h*`-polynomial (Ehrhart `δ`-polynomial). -/
  h : Polynomial ℤ
  /-- `h*_0 = 1`: the normalization satisfied by every lattice polytope. -/
  coeff_zero : h.coeff 0 = 1
  /-- Stanley nonnegativity of the `h*`-vector. -/
  nonneg : ∀ i, 0 ≤ h.coeff i
  /-- The Gorenstein criterion: the `h*`-vector is symmetric (palindromic). -/
  symm : h.reverse = h

namespace GorensteinHStar

/-- The **join** of two Gorenstein `h*`-data, modeled by multiplying the
`h*`-polynomials. This reflects the classical Ehrhart identity
`h*_{P ∗ Q} = h*_P · h*_Q`. The construction is total: it produces another
`GorensteinHStar`, i.e. the join of Gorenstein polytopes is Gorenstein. -/
noncomputable def join (P Q : GorensteinHStar) : GorensteinHStar where
  h := P.h * Q.h
  coeff_zero := by
    rw [mul_coeff_zero, P.coeff_zero, Q.coeff_zero, one_mul]
  nonneg := by
    intro i
    rw [coeff_mul]
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (P.nonneg x.1) (Q.nonneg x.2)
  symm := by
    rw [reverse_mul_of_domain, P.symm, Q.symm]









end GorensteinHStar

/-! ## Concrete examples (computational evidence)

We exhibit small Gorenstein `h*`-data corresponding to genuine reflexive/Gorenstein
polytopes and confirm the join stays in the class. -/

/-- The point (and the empty reflexive simplex): `h* = 1`. -/
noncomputable def hstarPoint : GorensteinHStar where
  h := 1
  coeff_zero := by simp
  nonneg := by
    intro i
    rw [coeff_one]
    split <;> norm_num
  symm := by rw [show (1 : Polynomial ℤ) = C 1 by simp, reverse_C]



/-! ## Contrast: the free sum can break symmetry

The naive intuition behind the mission title is real, but it applies to the *free sum*
`P ⊕ Q`, whose `h*`-polynomial is NOT the product of the factors' `h*`. Concatenating two
symmetric `h*`-vectors (a crude stand-in for a non-multiplicative combination) generally
yields an asymmetric vector. We make this concrete: the coefficient list `[1, 1, 1, 0, 0]`
arising from a degenerate "stacking" is not palindromic, witnessing that operations other
than the join need not preserve the Gorenstein property. -/


end GorensteinJoin


