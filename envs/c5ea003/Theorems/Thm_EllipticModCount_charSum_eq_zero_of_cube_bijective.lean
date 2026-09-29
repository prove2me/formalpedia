-- Prove2me | Theorems.Thm_EllipticModCount_charSum_eq_zero_of_cube_bijective
-- name    : EllipticModCount.charSum_eq_zero_of_cube_bijective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:11:53.947609+00:00
-- url     : https://prove2.me/theorems/4bb88af5-5ec4-4b64-98c8-ccab4348f888
-- title:
--   If cubing is a bijection of `F`, the curve `y^2 = x^3 + b` is *supersingular*:
-- statement:
--   If cubing is a bijection of `F`, the curve `y^2 = x^3 + b` is *supersingular*:
--   its character sum vanishes.
--
--   ```lean
--   theorem EllipticModCount.charSum_eq_zero_of_cube_bijective(hF : ringChar F ≠ 2)
--       (hcube : Function.Bijective fun x : F => x ^ 3) (b : F) : charSum 0 b = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticPointCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticPointCount.lean#L244

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

theorem EllipticModCount.charSum_eq_zero_of_cube_bijective(hF : ringChar F ≠ 2)
    (hcube : Function.Bijective fun x : F => x ^ 3) (b : F) : charSum 0 b = 0 := by sorry
