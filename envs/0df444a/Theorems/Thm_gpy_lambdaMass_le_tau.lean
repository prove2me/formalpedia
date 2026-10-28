-- Prove2me | Theorems.Thm_gpy_lambdaMass_le_tau
-- name    : gpy_lambdaMass_le_tau
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:18:38.033289+00:00
-- url     : https://prove2.me/theorems/cdcd36c1-e2fe-4b2c-b10d-b5ce2af8f73a
-- title:
--   Selberg λ-mass bound via τ-moments
-- statement:
--   For tuple size k+1, level R ≥ 2, and any degree, the total Selberg λ-mass Λ = ∑_{d,e} |λ_d λ_e| over the tuple support is at most (R·(1 + log R)^k)². This replaces the crude bound Λ ≤ R^{2k+2} obtained from the support size alone, saving roughly a factor R^{2k}; it follows from the exact τ-weighted identity for Λ and the Selberg mass sum bound.
-- source:
--   GPY τ-moment / divisor-sum estimates for Selberg weights, formalized from Mathlib (divisor double count, harmonic bound, divisor convolution, and the τ-weighted λ-mass identity)

import Mathlib
open Classical

theorem gpy_lambdaMass_le_tau {k R deg : ℕ} (hR : 2 ≤ R) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      |(if ∏ i, d i ≤ R then
          (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
            * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ deg
          else 0)
        * (if ∏ i, e i ≤ R then
          (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
            * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ deg
          else 0)|)
      ≤ ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ k) ^ 2 := by sorry
