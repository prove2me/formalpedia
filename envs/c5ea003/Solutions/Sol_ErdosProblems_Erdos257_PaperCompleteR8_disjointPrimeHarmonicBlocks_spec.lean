-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.disjointPrimeHarmonicBlocks_spec
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:34:50.465233+00:00
-- url     : https://prove2.me/submissions/c7198cf3-bd2f-4f59-be2b-8075f52cd6e6

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

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset









theorem chosenPrimeHarmonicBlock_spec (B : Finset ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (∀ p ∈ chosenPrimeHarmonicBlock B R hR, Nat.Prime p ∧ 2 < p ∧ p ∉ B) ∧
    R ≤ ∑ p ∈ chosenPrimeHarmonicBlock B R hR, (1 : ℝ) / p ∧
    (∑ p ∈ chosenPrimeHarmonicBlock B R hR, (1 : ℝ) / p) ≤ R + 1 :=
  Classical.choose_spec (exists_odd_prime_harmonic_block B R hR)





theorem primeBlockForbidden_mono (R : ℕ → ℝ) (hR : ∀ k, 0 ≤ R k) :
    Monotone (primeBlockForbidden R hR) := by
  apply monotone_nat_of_le_succ
  intro k
  exact subset_union_left
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (R : ℕ → ℝ) (hR : ∀ k, 0 ≤ R k) :
    Pairwise (fun k l => Disjoint (disjointPrimeHarmonicBlock R hR k)
      (disjointPrimeHarmonicBlock R hR l)) ∧
    ∀ k, (∀ p ∈ disjointPrimeHarmonicBlock R hR k, Nat.Prime p ∧ 2 < p) ∧
      R k ≤ ∑ p ∈ disjointPrimeHarmonicBlock R hR k, (1 : ℝ) / p ∧
      (∑ p ∈ disjointPrimeHarmonicBlock R hR k, (1 : ℝ) / p) ≤ R k + 1 := by
  have hspec := fun k => chosenPrimeHarmonicBlock_spec
    (primeBlockForbidden R hR k) (R k) (hR k)
  have hlt : ∀ k l, k < l → Disjoint (disjointPrimeHarmonicBlock R hR k)
      (disjointPrimeHarmonicBlock R hR l) := by
    intro k l hkl
    apply disjoint_left.mpr
    intro p hp hk
    have hnext : p ∈ primeBlockForbidden R hR (k + 1) :=
      mem_union_right _ hp
    have hforbid := primeBlockForbidden_mono R hR (Nat.succ_le_of_lt hkl) hnext
    exact ((hspec l).1 p hk).2.2 hforbid
  constructor
  · intro k l hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact hlt k l h
    · exact (hlt l k h).symm
  · intro k
    exact ⟨fun p hp => ⟨((hspec k).1 p hp).1, ((hspec k).1 p hp).2.1⟩,
      (hspec k).2⟩
end
