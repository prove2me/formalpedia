-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_separating_prime_blocks
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.exists_separating_prime_blocks
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:26:29.095516+00:00
-- url     : https://prove2.me/theorems/03a60370-aae4-49f1-b609-b5d18e794fd8
-- title:
--   Separated odd-prime blocks meet harmonic windows
-- statement:
--   There exist pairwise disjoint finite blocks P_k of odd primes with reciprocal-prime sum between 2^k and 2^k+1 for every k.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/PrimeHarmonicBlocks.lean#L142-L150
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.exists_separating_prime_blocks :
    ∃ P : ℕ → Finset ℕ, Pairwise (fun k l => Disjoint (P k) (P l)) ∧
      ∀ k, (∀ p ∈ P k, Nat.Prime p ∧ 2 < p) ∧
        (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p ∧
        (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1 := by sorry
end
