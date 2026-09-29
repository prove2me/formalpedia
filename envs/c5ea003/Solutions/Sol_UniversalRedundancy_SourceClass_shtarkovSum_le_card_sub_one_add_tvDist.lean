-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.shtarkovSum_le_card_sub_one_add_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T16:59:45.697846+00:00
-- url     : https://prove2.me/submissions/34f1a79a-ce48-46ba-bbc9-1b50dc6e63c8

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ]
    (S : SourceClass X Θ) {θ θ' : Θ} (hne : θ ≠ θ') :
    S.shtarkovSum ≤ (Fintype.card Θ : ℝ) - 1 + tvDist (S.prob θ) (S.prob θ') := by
  classical
  have hle1 : ∀ θ x, S.prob θ x ≤ 1 := by
    intro θ x
    rw [← S.sum_one θ]
    exact Finset.single_le_sum (f := fun x => S.prob θ x) (fun y _ => S.nonneg θ y) (Finset.mem_univ x)
  have hbdd : ∀ x, BddAbove (Set.range fun θ => S.prob θ x) := fun x =>
    ⟨1, by rintro _ ⟨θ, rfl⟩; exact hle1 θ x⟩
  have hle : ∀ θ x, S.prob θ x ≤ S.maxLik x := fun θ x => le_ciSup (hbdd x) θ
  have hml0 : ∀ x, 0 ≤ S.maxLik x := by
    intro x
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    exact (S.nonneg θ₀ x).trans (hle θ₀ x)
  have hone_le : 1 ≤ S.shtarkovSum := by
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    rw [← S.sum_one θ₀]
    exact Finset.sum_le_sum (fun x _ => hle θ₀ x)
  have hCpos : 0 < S.shtarkovSum := by linarith
  have hpt : ∀ x, S.maxLik x ≤ ∑ t ∈ Finset.univ \ {θ, θ'}, S.prob t x
      + max (S.prob θ x) (S.prob θ' x) := by
    intro x
    have hR0 : 0 ≤ ∑ t ∈ Finset.univ \ {θ, θ'}, S.prob t x := Finset.sum_nonneg (fun t _ => S.nonneg t x)
    refine ciSup_le (fun t => ?_)
    by_cases ht : t ∈ Finset.univ \ {θ, θ'}
    · have := Finset.single_le_sum (f := fun t => S.prob t x) (fun t _ => S.nonneg t x) ht
      have hM0 : 0 ≤ max (S.prob θ x) (S.prob θ' x) := le_max_of_le_left (S.nonneg θ x)
      simp only at this
      linarith
    · have htt : t = θ ∨ t = θ' := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_not] at ht
        exact ht
      rcases htt with rfl | rfl
      · linarith [le_max_left (S.prob t x) (S.prob θ' x)]
      · linarith [le_max_right (S.prob θ x) (S.prob t x)]
  have hmax : ∀ a b : ℝ, max a b = (a + b + |a - b|) / 2 := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
      ring
  have h2 : 2 ≤ Fintype.card Θ := by
    have := Finset.card_le_univ ({θ, θ'} : Finset Θ)
    rwa [Finset.card_pair hne] at this
  have hRcard : ((Finset.univ \ {θ, θ'} : Finset Θ).card : ℝ) = Fintype.card Θ - 2 := by
    have hc : (Finset.univ \ {θ, θ'} : Finset Θ).card = Fintype.card Θ - 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_pair hne]
    rw [hc, Nat.cast_sub h2]
    norm_num
  unfold SourceClass.shtarkovSum tvDist
  calc ∑ x, S.maxLik x
      ≤ ∑ x, (∑ t ∈ Finset.univ \ {θ, θ'}, S.prob t x + max (S.prob θ x) (S.prob θ' x)) :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ t ∈ Finset.univ \ {θ, θ'}, ∑ x, S.prob t x
        + ∑ x, (S.prob θ x + S.prob θ' x + |S.prob θ x - S.prob θ' x|) / 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp only [hmax]
    _ = (Fintype.card Θ : ℝ) - 1 + (∑ x, |S.prob θ x - S.prob θ' x|) / 2 := by
        simp only [S.sum_one, Finset.sum_const, nsmul_eq_mul, mul_one, hRcard]
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, S.sum_one, S.sum_one]
        ring
