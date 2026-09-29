-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
-- name    : ErdosProblems_Erdos257_PaperCompleteR8_PrimeHarmonicBlocks
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:44:31.067056+00:00
-- url     : https://prove2.me/theorems/5da954b6-7617-474d-b457-2f3bbf3e42b8
-- title:
--   Disjoint odd-prime harmonic block construction
-- statement:
--   This bundle chooses finite odd-prime harmonic blocks, recursively accumulates previously chosen primes into a forbidden set, and defines the kth block disjoint from earlier ones. Its retained existence theorems provide the choices under nonnegative requested mass.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/PrimeHarmonicBlocks.lean#L1-L153
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

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

/-- Nonnegative finite masses with atoms at most one have a threshold subset. -/
theorem exists_subset_mass_between {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ a ∈ S, f a ≤ 1) (hS : R ≤ ∑ a ∈ S, f a) :
    ∃ T ⊆ S, R ≤ ∑ a ∈ T, f a ∧ (∑ a ∈ T, f a) ≤ R + 1 := by
  revert hf hS
  induction S using Finset.induction_on with
  | empty =>
    intro hf hS
    exact ⟨∅, by simp, by simpa using hS, by simp only [sum_empty]; linarith⟩
  | @insert a S ha ih =>
    intro hf hS
    by_cases htail : R ≤ ∑ b ∈ S, f b
    · obtain ⟨T, hTS, hlow, hupp⟩ := ih (fun b hb => hf b (mem_insert_of_mem hb)) htail
      exact ⟨T, hTS.trans (subset_insert a S), hlow, hupp⟩
    · refine ⟨insert a S, subset_rfl, hS, ?_⟩
      rw [sum_insert ha]
      have hfa := hf a (mem_insert_self a S)
      have ht := lt_of_not_ge htail
      linarith

/-- Removing a finite set does not bound reciprocal-prime finite sums. -/
theorem exists_prime_mass_outside (E : Finset Nat.Primes) (R : ℝ) :
    ∃ S : Finset Nat.Primes, Disjoint S E ∧ R < ∑ p ∈ S, (1 / p : ℝ) := by
  classical
  by_contra h
  push_neg at h
  apply Nat.Primes.not_summable_one_div
  apply summable_of_sum_le (c := R + ∑ p ∈ E, (1 / p : ℝ))
    (fun p : Nat.Primes => one_div_nonneg.mpr (Nat.cast_nonneg (p : ℕ)))
  intro S
  have htail : (∑ p ∈ S \ E, (1 / p : ℝ)) ≤ R := h (S \ E) sdiff_disjoint
  have hhead : (∑ p ∈ S ∩ E, (1 / p : ℝ)) ≤ ∑ p ∈ E, (1 / p : ℝ) :=
    sum_le_sum_of_subset_of_nonneg inter_subset_right
      (fun p _ _ => one_div_nonneg.mpr (Nat.cast_nonneg (p : ℕ)))
  have hset : S \ (S ∩ E) = S \ E := by ext p; simp only [mem_sdiff, mem_inter]; tauto
  have hsplit := sum_sdiff (f := fun p : Nat.Primes => (1 / p : ℝ))
    (show S ∩ E ⊆ S from inter_subset_left)
  rw [hset] at hsplit
  linarith

/-- Finite odd-prime blocks avoid arbitrary forbidden integers and have controlled mass. -/
theorem exists_odd_prime_harmonic_block (B : Finset ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p ∧ 2 < p ∧ p ∉ B) ∧
      R ≤ ∑ p ∈ P, (1 : ℝ) / p ∧ (∑ p ∈ P, (1 : ℝ) / p) ≤ R + 1 := by
  classical
  let E : Finset Nat.Primes := (insert 2 B).subtype Nat.Prime
  obtain ⟨S, hSE, hmass⟩ := exists_prime_mass_outside E R
  have hatom : ∀ p ∈ S, (1 / p : ℝ) ≤ 1 := by
    intro p hp
    have hpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
    apply (div_le_one hpos).2
    exact_mod_cast p.property.one_lt.le
  obtain ⟨T, hTS, hlow, hupp⟩ := exists_subset_mass_between S
    (fun p : Nat.Primes => (1 / p : ℝ)) R hR hatom hmass.le
  let P : Finset ℕ := T.image (fun p : Nat.Primes => (p : ℕ))
  have hsum : (∑ p ∈ P, (1 : ℝ) / p) = ∑ p ∈ T, (1 / p : ℝ) := by
    dsimp [P]
    rw [sum_image]
    intro a ha b hb hab
    exact Subtype.ext hab
  refine ⟨P, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    have hnot : q ∉ E := fun hh => (disjoint_left.mp hSE) (hTS hq) hh
    have hnot' : (q : ℕ) ∉ insert 2 B := by
      intro hmem
      exact hnot (Finset.mem_subtype.mpr hmem)
    have hne : (q : ℕ) ≠ 2 := fun hh => hnot' (by simp [hh])
    have htwo := q.property.two_le
    exact ⟨q.property, by omega, fun hh => hnot' (mem_insert_of_mem hh)⟩
  · simpa only [hsum] using hlow
  · simpa only [hsum] using hupp

def chosenPrimeHarmonicBlock (B : Finset ℕ) (R : ℝ) (hR : 0 ≤ R) : Finset ℕ :=
  Classical.choose (exists_odd_prime_harmonic_block B R hR)



def primeBlockForbidden (R : ℕ → ℝ) (hR : ∀ k, 0 ≤ R k) : ℕ → Finset ℕ
  | 0 => ∅
  | k + 1 => primeBlockForbidden R hR k ∪
      chosenPrimeHarmonicBlock (primeBlockForbidden R hR k) (R k) (hR k)

def disjointPrimeHarmonicBlock (R : ℕ → ℝ) (hR : ∀ k, 0 ≤ R k) (k : ℕ) : Finset ℕ :=
  chosenPrimeHarmonicBlock (primeBlockForbidden R hR k) (R k) (hR k)







end ErdosProblems.Erdos257.PaperCompleteR8
end


