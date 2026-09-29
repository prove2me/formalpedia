-- Prove2me | Theorems.Thm_EllipticModCount_card_affineLocus
-- name    : EllipticModCount.card_affineLocus
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:11:38.617679+00:00
-- url     : https://prove2.me/theorems/f4bba3bd-ea5b-41ac-bc53-a0a1b0241130
-- title:
--   Counting formula.
-- statement:
--   **Counting formula.** The number of affine solutions of `y^2 = x^3+a*x+b` is
--   `#F + ∑ x, χ(x^3+a*x+b)`.
--
--   ```lean
--   theorem EllipticModCount.card_affineLocus(hF : ringChar F ≠ 2) (a b : F) :
--       ((affineLocus a b).card : ℤ) = (Fintype.card F : ℤ) + charSum a b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticPointCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticPointCount.lean#L72

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

theorem EllipticModCount.card_affineLocus(hF : ringChar F ≠ 2) (a b : F) :
    ((affineLocus a b).card : ℤ) = (Fintype.card F : ℤ) + charSum a b := by sorry
