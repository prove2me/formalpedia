-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_divisorFrameBudget_le_geometric
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.divisorFrameBudget_le_geometric
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:24:46.616775+00:00
-- url     : https://prove2.me/theorems/2e7498ad-59ef-4abc-89ff-10cafb172929
-- title:
--   Divisor-frame budget has a geometric bound
-- statement:
--   For a finite set P of primes whose reciprocal sum is at most 2^k+1, the associated divisor-frame budget is at most 6·(3/16)^k.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorFrameWeightedBudget.lean#L116-L152
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.divisorFrameBudget_le_geometric (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : (∑ p ∈ P, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) :
    divisorFrameBudget P k ≤ 6 * (3 / 16 : ℝ) ^ k := by sorry
end
