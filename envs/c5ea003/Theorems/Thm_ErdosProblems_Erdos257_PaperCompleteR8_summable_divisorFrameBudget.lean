-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_summable_divisorFrameBudget
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.summable_divisorFrameBudget
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:26:19.648934+00:00
-- url     : https://prove2.me/theorems/14830ca0-da65-404a-ad4a-baaef923feba
-- title:
--   Divisor-frame budgets are summable
-- statement:
--   If each P(k) is a finite prime set with reciprocal-prime sum at most 2^k+1, then the sequence of divisorFrameBudget(P(k),k) is summable.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorFrameWeightedBudget.lean#L154-L166
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.summable_divisorFrameBudget (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p)
    (hS : ∀ k, (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) :
    Summable (fun k => divisorFrameBudget (P k) k) := by sorry
end
