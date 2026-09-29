-- Prove2me | Theorems.Thm_EllipticModCount_sum_a_correlation
-- name    : EllipticModCount.sum_a_correlation
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:11:33.265046+00:00
-- url     : https://prove2.me/theorems/f16411b0-a7d0-4d7f-9e75-2b4c0e0310e5
-- title:
--   The `a`-sum of the two-point correlation.
-- statement:
--   The `a`-sum of the two-point correlation.
--
--   ```lean
--   theorem EllipticModCount.sum_a_correlation(x y : F) :
--       ∑ a : F, (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1)
--         = if x = y then (Fintype.card F : ℤ) ^ 2 - (Fintype.card F : ℤ) else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticSecondMoment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticSecondMoment.lean#L140

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

theorem EllipticModCount.sum_a_correlation(x y : F) :
    ∑ a : F, (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1)
      = if x = y then (Fintype.card F : ℤ) ^ 2 - (Fintype.card F : ℤ) else 0 := by sorry
