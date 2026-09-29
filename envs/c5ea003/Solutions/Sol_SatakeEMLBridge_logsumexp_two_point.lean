-- Prove2me | solution 1 for SatakeEMLBridge.logsumexp_two_point
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:41:33.219673+00:00
-- url     : https://prove2.me/submissions/db338035-6337-4153-9303-eef6e4ced0a5

-- Sol generated from Bridges/SatakeEMLBridge.lean
import Mathlib
import Definitions.Def_Bridges_SatakeEMLBridge

/-! # Satake-EML Bridge: Softmax Convergence to Tropical Max

Bridges the tropical Satake isomorphism (Tropical/Langlands/SatakeIsomorphism)
with EML-LogSumExp connections (Bridges/EMLTropicalBridge), proving that
the "soft" (LogSumExp) Satake image converges to the hard (tropical max)
Satake image as temperature → 0⁺.

Main results:
1. `logsumexp_two_point`: log(exp(a)+exp(b)) = max(a,b) + log(1+exp(-|a-b|))
2. `softMax_decomposition`: softMax(c,x₁,x₂) = max(x₁,x₂) + (1/c)·log(1+exp(-c·|x₁-x₂|))
3. `softMax_gap_upper`: softMax - max ≤ (1/c)·log 2
4. `softMax_ge_max`: max ≤ softMax
5. `softMax_same`: softMax(c,a,a) = a + (log 2)/c
6. `satake_soft_gap`: n·softMax - n·max ≤ (n/c)·log 2
7. `soft_satake_ge_hard`: n·max ≤ n·softMax

These establish the dequantization bridge: as temperature → 0⁺,
softmax converges to hardmax, connecting the classical Langlands program
to tropical geometry through the Satake isomorphism.

The key insight is that the tropical Satake isomorphism computes
`satakeImage n x₁ x₂ = n · max(x₁, x₂)`, while the smooth (classical)
version is `softMax c x₁ x₂` with explicit error bounds that shrink
as temperature increases. This provides a rigorous quantitative foundation
for "tropicalization as zero-temperature limit" in representation theory.
-/

noncomputable section

open Real

open SatakeEMLBridge

/-! ## 1. Soft Maximum Definition -/


/-! ## 2. LogSumExp Two-Point Identity -/

private theorem logsumexp_le (a b : ℝ) (_ : a ≤ b) :
    log (exp a + exp b) = b + log (1 + exp (a - b)) := by
  have hfac : exp a + exp b = exp b * (1 + exp (a - b)) := by
    have h1 : exp a = exp (b + (a - b)) := by congr 1; ring
    rw [h1, exp_add b (a - b)]
    ring_nf
  rw [hfac]
  have h1 : exp b ≠ 0 := ne_of_gt (exp_pos b)
  have h2 : (1 + exp (a - b)) ≠ 0 := by linarith [exp_pos (a - b)]
  rw [log_mul h1 h2, log_exp]

private theorem logsumexp_ge (a b : ℝ) (_ : b ≤ a) :
    log (exp a + exp b) = a + log (1 + exp (b - a)) := by
  have hfac : exp a + exp b = exp a * (1 + exp (b - a)) := by
    have h1 : exp b = exp (a + (b - a)) := by congr 1; ring
    rw [h1, exp_add a (b - a)]
    ring_nf
  rw [hfac]
  have h1 : exp a ≠ 0 := ne_of_gt (exp_pos a)
  have h2 : (1 + exp (b - a)) ≠ 0 := by linarith [exp_pos (b - a)]
  rw [log_mul h1 h2, log_exp]


/-! ## 3. Softmax Equality Case -/


/-! ## 4. Softmax Decomposition -/



/-! ## 5. Softmax-Hardmax Gap Bounds -/




/-! ## 6. Bridge to Satake Isomorphism -/





open SatakeEMLBridge in
theorem solution(a b : ℝ) :
    log (exp a + exp b) = max a b + log (1 + exp (-|a - b|)) := by
  cases le_total a b with
  | inl hab =>
    rw [max_eq_right hab, logsumexp_le a b hab]
    congr 1; congr 1; congr 1
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
    ring
  | inr hba =>
    rw [max_eq_left hba, logsumexp_ge a b hba]
    congr 1; congr 1; congr 1
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    ring
