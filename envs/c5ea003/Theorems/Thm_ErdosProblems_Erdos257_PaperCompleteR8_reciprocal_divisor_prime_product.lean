-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_reciprocal_divisor_prime_product
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.reciprocal_divisor_prime_product
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:24:36.595482+00:00
-- url     : https://prove2.me/theorems/4de2d993-ffbb-41f1-86f4-227d93e192fb
-- title:
--   Reciprocal divisors of a prime product have a product formula
-- statement:
--   For a finite set P of primes, the sum of reciprocals over the divisors of the product of P equals the product over p in P of (1+1/p).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorFrameWeightedBudget.lean#L60-L75
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.reciprocal_divisor_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) =
      ∏ p ∈ P, (1 + (1 : ℝ) / p) := by sorry
end
