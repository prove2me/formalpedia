-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_disjointPrimeHarmonicBlocks_spec
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.disjointPrimeHarmonicBlocks_spec
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:17:52.628048+00:00
-- url     : https://prove2.me/theorems/e67e538d-0781-4504-8beb-b5f539f8ab10
-- title:
--   Disjoint odd-prime blocks realize harmonic targets
-- statement:
--   Given any sequence of nonnegative targets R_k, there are pairwise disjoint finite blocks of odd primes whose reciprocal-prime sums lie between R_k and R_k+1 for every k.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/PrimeHarmonicBlocks.lean#L115-L140
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

/-!
# Prime harmonic blocks with bounded overshoot

Reciprocal-prime divergence supplies a finite block beyond any finite forbidden
set. A finite threshold-crossing argument limits overshoot to one. Recursive
exclusion of all earlier blocks then gives pairwise disjoint odd-prime blocks
at any prescribed nonnegative harmonic scales. No weighted or logarithmic
moment assertion about their divisor frames is assumed here.
-/
noncomputable section
open Finset

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.disjointPrimeHarmonicBlocks_spec (R : ℕ → ℝ) (hR : ∀ k, 0 ≤ R k) :
    Pairwise (fun k l => Disjoint (disjointPrimeHarmonicBlock R hR k)
      (disjointPrimeHarmonicBlock R hR l)) ∧
    ∀ k, (∀ p ∈ disjointPrimeHarmonicBlock R hR k, Nat.Prime p ∧ 2 < p) ∧
      R k ≤ ∑ p ∈ disjointPrimeHarmonicBlock R hR k, (1 : ℝ) / p ∧
      (∑ p ∈ disjointPrimeHarmonicBlock R hR k, (1 : ℝ) / p) ≤ R k + 1 := by sorry
end
