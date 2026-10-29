-- Prove2me | Theorems.Thm_gpy_lambdaMass_minimal
-- name    : gpy_lambdaMass_minimal
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T21:47:52.478998+00:00
-- url     : https://prove2.me/theorems/19b648f5-cf27-4019-9d10-cd09fd7acb94
-- title:
--   Minimal weights: λ-mass bound
-- statement:
--   For level R ≥ 2 and any exponent kk, the total λ-mass of the minimal tuple weights λ_d = (∏ᵢ μ(dᵢ)) · (1 − log(∏ᵢ dᵢ)/log R)^kk, truncated to zero when ∏ᵢ dᵢ > R, satisfies Λ = ∑_{d,e} |λ_d λ_e| ≤ R^(2k), where the sum runs over support pairs of tuples with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. This follows from |λ| ≤ 1 on the support and the support having at most R^k elements. Honest scope note: this crude bound does NOT close the GPY argument for any kk — with it, the BV error term is of order R^(2k+2) · Y · log^(−A′) against a main term at most of order R^(2k) · Y, so there is no separation. It is a foundation/mass-bound result, not a separation claim.
-- source:
--   GPY minimal polynomial-truncated lambda weights: crude total lambda-mass bound Lambda <= R^(2k)

import Mathlib
open Classical

theorem gpy_lambdaMass_minimal {k R kk : ℕ} (hR : 2 ≤ R) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        abs (((∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)) *
            (if ∏ i, d i ≤ R then
              (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ kk
            else 0))
          * ((∏ i, ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)) *
            (if ∏ i, e i ≤ R then
              (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ kk
            else 0))))
      ≤ (R : ℝ) ^ (2 * k) := by sorry
