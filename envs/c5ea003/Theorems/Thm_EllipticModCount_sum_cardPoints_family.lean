-- Prove2me | Theorems.Thm_EllipticModCount_sum_cardPoints_family
-- name    : EllipticModCount.sum_cardPoints_family
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:13:20.65321+00:00
-- url     : https://prove2.me/theorems/6bacc080-87d7-46ed-891e-6fe9d607f068
-- title:
--   Exact total point count of the whole family.
-- statement:
--   **Exact total point count of the whole family.** Summing over all `q^2` short
--   Weierstrass equations gives exactly `q^2 * (q+1)` points, i.e. the average curve has
--   exactly `q + 1` points.
--
--   ```lean
--   theorem EllipticModCount.sum_cardPoints_family(hF : ringChar F ≠ 2) :
--       ∑ a : F, ∑ b : F, (cardPoints a b : ℤ)
--         = (Fintype.card F : ℤ) ^ 2 * ((Fintype.card F : ℤ) + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticSecondMoment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticSecondMoment.lean#L312

-- Thm stub generated from Combinatorics/EllipticSecondMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
/-
# The exact second moment of the trace of Frobenius over a finite field

Let `F` be a finite field of odd characteristic, `q = #F`, and for `a b : F` let
`a(a,b)` be the trace of Frobenius of the short Weierstrass curve `y^2 = x^3+a*x+b`
(defined in `Combinatorics.EllipticPointCount`).  We prove the **exact** identity

`∑_{a,b ∈ F} a(a,b)^2 = q^3 - q^2`,

together with its Chebyshev consequence: the number of parameter pairs `(a,b)` with
`a(a,b)^2 ≥ K` is at most `(q^3 - q^2)/K`.  In particular *almost all* curves in the
family satisfy the Hasse bound `|a| ≤ 2√q`, by a purely elementary character-sum
computation (no Weil conjectures, no Riemann–Roch).

The engine is the elementary evaluation of the quadratic character sum of a
separable quadratic, `EllipticModCount.sum_char_mul_shift`.

Main results:

* `EllipticModCount.sum_char_mul_shift` : `∑_c χ(c(c+w)) = -1` for `w ≠ 0`.
* `EllipticModCount.sum_char_shift_pair` : `∑_b χ((b+u)(b+v)) = q-1` or `-1`.
* `EllipticModCount.second_moment_charSum` : `∑_{a,b} S(a,b)^2 = q^3 - q^2`.
* `EllipticModCount.second_moment_frobTrace` : the same for the trace of Frobenius.
* `EllipticModCount.card_large_frobTrace_le` : Chebyshev / "Hasse on average".
-/

open EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem EllipticModCount.sum_cardPoints_family(hF : ringChar F ≠ 2) :
    ∑ a : F, ∑ b : F, (cardPoints a b : ℤ)
      = (Fintype.card F : ℤ) ^ 2 * ((Fintype.card F : ℤ) + 1) := by sorry
