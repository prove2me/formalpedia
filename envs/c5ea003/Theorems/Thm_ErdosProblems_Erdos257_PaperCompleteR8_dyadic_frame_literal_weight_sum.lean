-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_frame_literal_weight_sum
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.dyadic_frame_literal_weight_sum
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:26:07.454572+00:00
-- url     : https://prove2.me/theorems/3d4a5cf4-7472-4c78-8d6e-94ebf73fed16
-- title:
--   Dyadic frame weight equals its reciprocal-divisor budget
-- statement:
--   For any M,k, the literal weighted sum over the associated dyadic divisor frame equals the reciprocal-divisor sum of M divided by 2^(2^(k+2))−1, with Lean's totalized division convention covering degenerate M.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorFrameWeightedBudget.lean#L93-L114
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
import Mathlib
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

/-!
# Divisor-product masses and the separating host's weighted frame budget

The reciprocal divisor sum is computed from the actual prime product. Its
exponential upper bound and the prescribed harmonic scales give a summable
sequence of literal dyadic frame weights. Identifying these literal weights
with the finite-prime weighted term uses the odd-cofactor valuation identity;
the divergent logarithmic moment is a separate remaining step.
-/
noncomputable section
open Finset

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.dyadic_frame_literal_weight_sum (M k : ℕ) :
    (∑ a ∈ dyadicDivisorFrame M k,
      ((2 : ℝ) ^ (k + 2)) / ((a : ℝ) * ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1))) =
    (∑ d ∈ M.divisors, (1 : ℝ) / d) /
      ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1) := by sorry
end
