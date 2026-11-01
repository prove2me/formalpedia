-- Prove2me | Theorems.Thm_gpy_sum_maxCoprimeErr_le_of_bvSumBound_range
-- name    : gpy_sum_maxCoprimeErr_le_of_bvSumBound_range
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T06:53:21.947217+00:00
-- url     : https://prove2.me/theorems/61f3b005-acd0-47a5-9154-7be423d5b466
-- title:
--   First moment over L at most R squared from a BV sum bound, conditional
-- statement:
--   Conditional on a plain Bombieri-Vinogradov-style sum bound with bound B at height Y' and on the level constraint R squared below Y' to the power one half minus eta, the first moment of the max coprime-residue errors over moduli L up to R squared is at most B. The BV hypothesis is an explicit hypothesis, not a proved fact. All local definitions are unfolded into Mathlib terms.
-- source:
--   GPY BDH-partial bounds (trivial second moment plus Cauchy-Schwarz with the tau-fourth bound), conditional on a plain BV sum bound; formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_sum_maxCoprimeErr_le_of_bvSumBound_range (M : ℕ → ℕ → ℝ) (Y' R : ℕ)
    {η : ℝ} (B : ℝ)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : (∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B)) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), (if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' h
    else 0) ≤ B := by sorry
