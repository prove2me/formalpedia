-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
-- name    : ErdosProblems_Erdos257_PaperCompleteR8_DivisorFrameWeightedBudget
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:52:22.01678+00:00
-- url     : https://prove2.me/theorems/07135028-9a06-4fe8-a228-cbeb0a1ab841
-- title:
--   Reciprocal-divisor frame budget
-- statement:
--   This bundle defines divisorFrameBudget(P,k) as the reciprocal-divisor sum of the product of P, divided by 2^(2^(k+2))−1.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorFrameWeightedBudget.lean#L1-L182
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
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
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset









def divisorFrameBudget (P : Finset ℕ) (k : ℕ) : ℝ :=
  (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) /
    ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1)









end ErdosProblems.Erdos257.PaperCompleteR8
end


