-- Prove2me | Theorems.Thm_gpy_lambdaMass_maynard
-- name    : gpy_lambdaMass_maynard
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T21:42:17.207001+00:00
-- url     : https://prove2.me/theorems/23d77811-23d8-4b1f-9bbc-2135ceaa8ea4
-- title:
--   Maynard weights: λ-mass bound
-- statement:
--   Let k be a tuple length, R a level, and m a degree. Let the Maynard weight be lam_d = (product over i of mu(d_i)) times the polynomial simplex cutoff (1 - sum_i log(d_i)/log R)^m when sum_i log(d_i)/log R <= 1, and 0 otherwise. Then the lambda-mass sum_{d, e in support} |lam_d * lam_e|, where the support is the set of tuples d with 1 <= d_i <= R and prod_i d_i <= R, is at most (R^k)^2. The per-term bound |lam_d| <= 1 is sharp; the final counting step (support size at most R^k) is not sharp, and the tau-weighted refinement replacing it is open. Honest scope note: the Maynard–Tao polynomial-subcase candidate does NOT close the GPY argument. Its singular-series evaluation (identifying the main-term coefficient with the singular series times the cutoff integral) still needs Mertens-type sum-to-integral estimates, local-factor computations, and tau-weighted divisor sums, and the sharp tau-weighted lambda-mass bound is likewise open. These are foundation and coefficient-identification results, not a separation claim; for the qualitative GPY conclusion (liminf gap/log -> 0) the Maynard machinery is arguably overkill.
-- source:
--   GPY Maynard-Tao weights (polynomial subcase): the lambda-mass bound, via |lambda_d| <= 1 and the support count bound

import Mathlib
open Classical

theorem gpy_lambdaMass_maynard (m R : ℕ) {k : ℕ} :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        abs (((∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (if ∑ i, Real.log (d i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (d i) / Real.log R) ^ m else 0))
          * ((∏ i, (ArithmeticFunction.moebius (e i) : ℝ)) *
            (if ∑ i, Real.log (e i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (e i) / Real.log R) ^ m else 0))))
      ≤ ((R : ℝ) ^ k) ^ 2 := by sorry
