-- Prove2me | Theorems.Thm_EulerTwoSquares_small_parts_sq_sum_ge
-- name    : EulerTwoSquares.small_parts_sq_sum_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:46:31.687365+00:00
-- url     : https://prove2.me/theorems/a54954e8-b718-4086-9766-ad9bc6ec2f6d
-- title:
--   The twisted parts cannot both be small.
-- statement:
--   **The twisted parts cannot both be small.**  For representations of two odd primes,
--   `B² + C² ≥ p + q - 1`, so `max(|B|,|C|) ≥ √((p+q-1)/2)`.  This is the arithmetic source of the
--   quartic search barrier: the second representation always sits far from the axes.
--
--   ```lean
--   theorem EulerTwoSquares.small_parts_sq_sum_ge{e f g h : ℤ} (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
--       (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hgh : g ^ 2 + h ^ 2 = (q : ℤ)) (hne1 : e ≠ f)
--       (hne2 : g ≠ h) :
--       (p : ℤ) + (q : ℤ) - 1 ≤ (e * h - f * g) ^ 2 + (e * g - f * h) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresDeterminism.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresDeterminism.lean#L201

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




/-! ## The two cross terms factor exactly -/



/-! ## Deterministic extraction -/




/-! ## The normalised (non-negative) form: the sign of `B*C` decides -/




/-! ## Where the four parts sit

The same two Brahmagupta identities also locate the parts themselves, which is what feeds the
quartic search barrier of `EulerTwoSquaresBarrier`. -/

theorem EulerTwoSquares.small_parts_sq_sum_ge{e f g h : ℤ} (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hgh : g ^ 2 + h ^ 2 = (q : ℤ)) (hne1 : e ≠ f)
    (hne2 : g ≠ h) :
    (p : ℤ) + (q : ℤ) - 1 ≤ (e * h - f * g) ^ 2 + (e * g - f * h) ^ 2 := by sorry
