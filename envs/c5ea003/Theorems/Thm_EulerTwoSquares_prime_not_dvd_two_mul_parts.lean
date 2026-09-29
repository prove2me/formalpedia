-- Prove2me | Theorems.Thm_EulerTwoSquares_prime_not_dvd_two_mul_parts
-- name    : EulerTwoSquares.prime_not_dvd_two_mul_parts
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:46:03.290714+00:00
-- url     : https://prove2.me/theorems/13cb28e8-a436-490f-b03b-2faef12e25a7
-- title:
--   An odd prime `p = e² + f²` does not divide `2 * e * f`.
-- statement:
--   An odd prime `p = e² + f²` does not divide `2 * e * f`.
--
--   ```lean
--   theorem EulerTwoSquares.prime_not_dvd_two_mul_parts(hp : p.Prime) (hp2 : p ≠ 2) {e f : ℤ}
--       (hef : e ^ 2 + f ^ 2 = (p : ℤ)) : ¬ ((p : ℤ) ∣ 2 * e * f) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresDeterminism.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresDeterminism.lean#L50

-- Thm stub generated from Algebra/EulerTwoSquaresDeterminism.lean
import Mathlib

/-!
# Which prime does Euler's step extract?

`EulerTwoSquaresCore.euler_gcd_pair_factors` shows that the two gcd's produced by Euler's
combination step multiply to `p * q`.  It does **not** say which of the two gcd's is `p` and
which is `q`.  This file settles that question completely for the Brahmagupta pair.

Write `p = e² + f²`, `q = g² + h²` and form the two representations of `N = p*q`

`A = e*g + f*h`, `B = e*h - f*g`,  `C = e*g - f*h`, `D = e*h + f*g`,

so that `A² + B² = C² + D² = N`.  Then the two cross terms factor *exactly*:

`A*D - B*C = 2*e*f*q`  and  `A*D + B*C = 2*g*h*p`   (`cross_sub_factors`, `cross_add_factors`).

Since an odd prime `p = e²+f²` divides neither `2`, nor `e`, nor `f`, these identities pin the
gcd's down on the nose:

`gcd(A*D - B*C, N) = q`  and  `gcd(A*D + B*C, N) = p`   (`gcd_cross_sub_eq_q`,
`gcd_cross_add_eq_p`).

So the extraction is *deterministic*, not merely proper: the signed cross term of the
Brahmagupta pair always yields the prime whose representation was **not** used in the "twist".
Working with normalised (non-negative) parts, `|B|·|C| = |B*C|`, so which prime comes out is
governed purely by the sign of `B*C = (e*h - f*g)(e*g - f*h)`
(`gcd_cross_abs_eq_q_of_pos`, `gcd_cross_abs_eq_p_of_neg`).  This is the sharpest possible
form of the "extraction always works" face of the Euler campaign.
-/


variable {p q : ℕ}

/-! ## An odd prime that is a sum of two squares divides neither part -/

theorem EulerTwoSquares.prime_not_dvd_two_mul_parts(hp : p.Prime) (hp2 : p ≠ 2) {e f : ℤ}
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) : ¬ ((p : ℤ) ∣ 2 * e * f) := by sorry
