-- Prove2me | Theorems.Thm_gpy_divWeightedErrSum_le_of_bvSumBound_bdh
-- name    : gpy_divWeightedErrSum_le_of_bvSumBound_bdh
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T07:01:40.573052+00:00
-- url     : https://prove2.me/theorems/a1457883-e376-46be-9935-4f370452e8d9
-- title:
--   Cauchy-Schwarz divisor-weighted bound from a BV sum bound, conditional
-- statement:
--   Conditional on a plain BV sum bound with bound B (nonnegative) and on the level constraint, the divisor-weighted error sum over moduli up to R squared is at most R times one plus log R squared to the power two to the four k, times B. With B of the shape C times Y' times a negative log power, this is R times a polylog times C times Y' times that log power: the factor R is the precise gap to the divisor-weighted target Cw times Y' times a negative log power, since R is a power of Y', not a polylog. This theorem therefore does NOT discharge hDiv. All local definitions are unfolded into Mathlib terms.
-- source:
--   GPY BDH-partial bounds (trivial second moment plus Cauchy-Schwarz with the tau-fourth bound), conditional on a plain BV sum bound; formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_divWeightedErrSum_le_of_bvSumBound_bdh (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    {η : ℝ} (B : ℝ) (hR : 1 ≤ R) (hBnn : 0 ≤ B)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : (∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B)) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter (fun d => ∏ i, d i = L)).card : ℝ) ^ 2 * (if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' h
    else 0)
      ≤ (R : ℝ) * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k)) * B := by sorry
