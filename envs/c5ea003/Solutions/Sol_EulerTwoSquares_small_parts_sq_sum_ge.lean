-- Prove2me | solution 1 for EulerTwoSquares.small_parts_sq_sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:03:37.244193+00:00
-- url     : https://prove2.me/submissions/2b841bb8-4919-40b6-ada1-8a4d87f3fef5

-- Sol generated from Algebra/EulerTwoSquaresDeterminism.lean
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

/-- The two "twisted" parts satisfy `B² + C² = N - 4efgh`. -/
theorem small_parts_sq_sum (e f g h : ℤ) :
    (e * h - f * g) ^ 2 + (e * g - f * h) ^ 2
      = (e ^ 2 + f ^ 2) * (g ^ 2 + h ^ 2) - 4 * e * f * g * h := by ring






theorem solution{e f g h : ℤ} (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hgh : g ^ 2 + h ^ 2 = (q : ℤ)) (hne1 : e ≠ f)
    (hne2 : g ≠ h) :
    (p : ℤ) + (q : ℤ) - 1 ≤ (e * h - f * g) ^ 2 + (e * g - f * h) ^ 2 := by
  have h1 : 1 ≤ (e - f) ^ 2 := by
    have : e - f ≠ 0 := sub_ne_zero.2 hne1
    rcases lt_or_gt_of_ne this with hlt | hgt
    · nlinarith
    · nlinarith
  have h2 : 1 ≤ (g - h) ^ 2 := by
    have : g - h ≠ 0 := sub_ne_zero.2 hne2
    rcases lt_or_gt_of_ne this with hlt | hgt
    · nlinarith
    · nlinarith
  have hef4 : 4 * (e * f) ≤ 2 * (p : ℤ) - 2 := by nlinarith
  have hgh4 : 4 * (g * h) ≤ 2 * (q : ℤ) - 2 := by nlinarith
  have hp1 : (1 : ℤ) ≤ (p : ℤ) := by nlinarith
  have hq1 : (1 : ℤ) ≤ (q : ℤ) := by nlinarith
  have hprod : 4 * (e * f) * (4 * (g * h)) ≤ (2 * (p : ℤ) - 2) * (2 * (q : ℤ) - 2) := by
    have hefpos : (0 : ℤ) ≤ 4 * (e * f) := by positivity
    have hghpos : (0 : ℤ) ≤ 4 * (g * h) := by positivity
    nlinarith
  rw [small_parts_sq_sum, hef, hgh]
  nlinarith
