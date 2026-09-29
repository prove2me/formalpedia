-- Prove2me | Theorems.Thm_EllipticModCount_charSum_eq_zero_of_neg_one_nonsquare
-- name    : EllipticModCount.charSum_eq_zero_of_neg_one_nonsquare
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:12:32.794528+00:00
-- url     : https://prove2.me/theorems/06ad5ee6-e8b2-4d8c-9458-073a3c217b0f
-- title:
--   If `-1` is a nonsquare in `F`, the curve `y^2 = x^3 + a*x` is *supersingular*.
-- statement:
--   If `-1` is a nonsquare in `F`, the curve `y^2 = x^3 + a*x` is *supersingular*.
--
--   ```lean
--   theorem EllipticModCount.charSum_eq_zero_of_neg_one_nonsquare(hneg : quadraticChar F (-1) = -1) (a : F) :
--       charSum a 0 = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticPointCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticPointCount.lean#L256

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

theorem EllipticModCount.charSum_eq_zero_of_neg_one_nonsquare(hneg : quadraticChar F (-1) = -1) (a : F) :
    charSum a 0 = 0 := by sorry
