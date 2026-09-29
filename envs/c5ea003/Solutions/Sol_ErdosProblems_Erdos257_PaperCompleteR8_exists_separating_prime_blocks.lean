-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.exists_separating_prime_blocks
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:35:46.705986+00:00
-- url     : https://prove2.me/submissions/4af9aa97-6aba-4026-b98c-b7eb19f55dd2

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_disjointPrimeHarmonicBlocks_spec
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

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution :
    ∃ P : ℕ → Finset ℕ, Pairwise (fun k l => Disjoint (P k) (P l)) ∧
      ∀ k, (∀ p ∈ P k, Nat.Prime p ∧ 2 < p) ∧
        (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p ∧
        (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1 := by
  let hR : ∀ k : ℕ, 0 ≤ (2 : ℝ) ^ k := fun k => by positivity
  exact ⟨disjointPrimeHarmonicBlock (fun k => (2 : ℝ) ^ k) hR,
    disjointPrimeHarmonicBlocks_spec (fun k => (2 : ℝ) ^ k) hR⟩
end
