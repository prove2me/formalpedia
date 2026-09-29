-- Prove2me | Theorems.Thm_EllipticModCount_two_dvd_cardPoints_iff
-- name    : EllipticModCount.two_dvd_cardPoints_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:13:17.138479+00:00
-- url     : https://prove2.me/theorems/71eab9bc-5531-4b34-9048-cf38429845b7
-- title:
--   2-torsion criterion.
-- statement:
--   **2-torsion criterion.** For a nonsingular curve, the number of points is even iff the
--   cubic `x^3+a*x+b` has a root in `F` (i.e. the curve has a nontrivial 2-torsion point).
--
--   ```lean
--   theorem EllipticModCount.two_dvd_cardPoints_iff(hF : ringChar F ≠ 2) (hd : disc a b ≠ 0) :
--       2 ∣ cardPoints a b ↔ ∃ x : F, x ^ 3 + a * x + b = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticPointCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticPointCount.lean#L212

-- Thm stub generated from Combinatorics/EllipticPointCount.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
/-
# Exact point counting and modular invariants for short Weierstrass curves

For a finite field `F` of odd characteristic and parameters `a b : F` we study the
affine locus of the short Weierstrass equation `y^2 = x^3 + a*x + b` together with
one point at infinity.  Everything is done by *elementary counting*: the basic tool
is the quadratic character `quadraticChar F`, which counts square roots.

Main results:

* `EllipticModCount.card_affineLocus` : the affine point count equals `#F + S(a,b)`
  where `S(a,b) = ∑ x, χ(x^3+a*x+b)`.
* `EllipticModCount.frobTrace_eq_neg_charSum` : the trace of Frobenius is `-S(a,b)`.
* `EllipticModCount.two_dvd_cardPoints_iff` : (**2-torsion criterion**) for a
  nonsingular curve the point count is even iff the cubic has a root in `F`.
* `EllipticModCount.rootSet_card_cases` : for a nonsingular curve the cubic has
  exactly `0`, `1` or `3` roots — never `2`.
* `EllipticModCount.cardPoints_eq_of_cube_bijective` : if cubing is a bijection
  (e.g. `p % 3 = 2`) then `y^2 = x^3 + b` has exactly `#F + 1` points.
* `EllipticModCount.cardPoints_eq_of_neg_one_nonsquare` : if `-1` is a nonsquare
  (e.g. `p % 4 = 3`) then `y^2 = x^3 + a*x` has exactly `#F + 1` points.
* `EllipticModCount.frobTrace_twist` : quadratic twisting negates the trace.
* `EllipticModCount.sum_frobTrace_eq_zero` : the trace averages to `0` over the
  family `b ↦ (a,b)`, and over the whole family `(a,b)`.
-/

open EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]




















variable {a b r s : F}

theorem EllipticModCount.two_dvd_cardPoints_iff(hF : ringChar F ≠ 2) (hd : disc a b ≠ 0) :
    2 ∣ cardPoints a b ↔ ∃ x : F, x ^ 3 + a * x + b = 0 := by sorry
