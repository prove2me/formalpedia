-- Prove2me | Theorems.Thm_gpy_sum_maxCoprimeErr_sq_le_of_bvSumBound_target
-- name    : gpy_sum_maxCoprimeErr_sq_le_of_bvSumBound_target
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T06:57:30.082982+00:00
-- url     : https://prove2.me/theorems/a6985597-cf49-403e-ae61-1a51a041a27f
-- title:
--   BDH-shaped bound in target form, conditional
-- statement:
--   Conditional on a BV sum bound of the target shape C times Y' times log Y' to the power minus A' at height Y' and on the level constraint, the sum of squares of the max coprime-residue errors over moduli up to R squared is at most C squared times Y' squared times log Y' to the power minus A', squared. All local definitions are unfolded into Mathlib terms.
-- source:
--   GPY BDH-partial bounds (trivial second moment plus Cauchy-Schwarz with the tau-fourth bound), conditional on a plain BV sum bound; formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_sum_maxCoprimeErr_sq_le_of_bvSumBound_target (M : ℕ → ℕ → ℝ) (Y' R : ℕ)
    {η : ℝ} (C A' : ℝ)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : (∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ C * ((Y' : ℝ) * Real.log (Y' : ℝ) ^ (-A')))) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), ((if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' h
    else 0)) ^ 2
      ≤ C ^ 2 * (Y' : ℝ) ^ 2 * (Real.log (Y' : ℝ) ^ (-A')) ^ 2 := by sorry
