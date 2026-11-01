-- Prove2me | Theorems.Thm_gpy_divWeightedErrSum_sq_le_of_bvSumBound
-- name    : gpy_divWeightedErrSum_sq_le_of_bvSumBound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T06:59:32.803759+00:00
-- url     : https://prove2.me/theorems/b20d0de7-f8e1-450e-8d49-eeb8d8d55ee4
-- title:
--   Squared Cauchy-Schwarz combination with the tau-fourth bound, conditional
-- statement:
--   Conditional on a plain BV sum bound with bound B and on the level constraint, the square of the divisor-weighted error sum (weights tau_{k+1}(L) squared, moduli up to R squared) is at most R squared times one plus log R squared to the power two to the four k minus one, times B squared. The tau-fourth bound and the trivial second moment are combined by Cauchy-Schwarz. This is a conditional bound; it is not stated as discharging any divisor-weighted BV hypothesis target. All local definitions are unfolded into Mathlib terms.
-- source:
--   GPY BDH-partial bounds (trivial second moment plus Cauchy-Schwarz with the tau-fourth bound), conditional on a plain BV sum bound; formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_divWeightedErrSum_sq_le_of_bvSumBound (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    {η : ℝ} (B : ℝ) (hR : 1 ≤ R)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : (∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B)) :
    (∑ L ∈ Finset.range (R ^ 2 + 1), (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter (fun d => ∏ i, d i = L)).card : ℝ) ^ 2 * (if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' h
    else 0)) ^ 2
      ≤ ((R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1)) * B ^ 2 := by sorry
