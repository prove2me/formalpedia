-- Prove2me | Theorems.Thm_gpy_divWeightedErrSum_le_of_genuineBDH_level
-- name    : gpy_divWeightedErrSum_le_of_genuineBDH_level
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T04:38:25.459366+00:00
-- url     : https://prove2.me/theorems/219f3b7a-3f1d-4e45-9901-7aadf4efcb76
-- title:
--   Level divisor-weighted error bound conditional on a genuine BDH hypothesis
-- statement:
--   CONDITIONAL on the explicit, unproved hypothesis hBDH (a genuine Barban-Davenport-Halberstam-shaped summed second-moment bound) and on the level constraint R squared below Y' to the power one half minus eta: the divisor-weighted error sum is at most Y' to the power one minus eta times sqrt of the explicit polylog factor. The remaining step to hDiv's target shape is only an asymptotic threshold inequality for large Y', which is NOT proved here. This does NOT prove genuine BDH and does NOT discharge hDiv.
-- source:
--   GPY genuine-BDH conditional reduction (GPYBDHFull.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_divWeightedErrSum_le_of_genuineBDH_level (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    {η : ℝ} (D : ℝ) (E : ℕ) (hD : 0 ≤ D) (hR : 1 ≤ R) (hY : 1 ≤ Y')
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBDH : ∑ L ∈ Finset.range (R ^ 2 + 1),
        ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
          (abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L)) ^ 2
        ≤ D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card : ℝ) ^ 2 * (if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L))).max' h
    else 0) ≤
      (Y' : ℝ) ^ (1 - η) *
        Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) * (1 + Real.log (Y' : ℝ)) ^ E) := by sorry
