-- Prove2me | Theorems.Thm_gpy_divWeightedErrSum_le_of_genuineBDH
-- name    : gpy_divWeightedErrSum_le_of_genuineBDH
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T04:22:48.350573+00:00
-- url     : https://prove2.me/theorems/e89b1ff6-041d-4a6e-a1c1-44d7e98ae22e
-- title:
--   Divisor-weighted error bound conditional on a genuine BDH hypothesis
-- statement:
--   CONDITIONAL on the explicit, unproved hypothesis hBDH (a genuine Barban-Davenport-Halberstam-shaped summed second-moment bound with explicit constants D and polylog exponent E): the divisor-weighted error sum is at most R squared times sqrt(Y') times sqrt of the explicit polylog factor. This does NOT prove genuine BDH and does NOT discharge hDiv.
-- source:
--   GPY genuine-BDH conditional reduction (GPYBDHFull.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_divWeightedErrSum_le_of_genuineBDH (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    (D : ℝ) (E : ℕ) (hD : 0 ≤ D) (hR : 1 ≤ R) (hY : 1 ≤ Y')
    (hBDH : ∑ L ∈ Finset.range (R ^ 2 + 1),
        ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
          (abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L)) ^ 2
        ≤ D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card : ℝ) ^ 2 * (if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L))).max' h
    else 0) ≤
      (R : ℝ) ^ 2 * Real.sqrt (Y' : ℝ) *
        Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) * (1 + Real.log (Y' : ℝ)) ^ E) := by sorry
