-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.shtarkovSum_eq_card_of_disjoint_supports
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T16:28:42.711634+00:00
-- url     : https://prove2.me/submissions/f715a60c-7e9a-43ad-bc10-38acbce146bf

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ] [Fintype Θ]
    (supp : Θ → Finset X) (hdisj : ∀ θ θ', θ ≠ θ' → Disjoint (supp θ) (supp θ'))
    (hmass : ∀ θ, ∑ x ∈ supp θ, S.prob θ x = 1) :
    S.shtarkovSum = (Fintype.card Θ : ℝ) := by
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
  have hout : ∀ θ x, x ∉ supp θ → S.prob θ x = 0 := by
    intro θ x hx
    have htot := Finset.sum_compl_add_sum (supp θ) (S.prob θ)
    rw [S.sum_one θ, hmass θ] at htot
    have hz : ∑ y ∈ (supp θ)ᶜ, S.prob θ y = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => S.nonneg θ y)).mp hz x (Finset.mem_compl.mpr hx)
  have hmlsum : ∀ x, S.maxLik x = ∑ θ, S.prob θ x := by
    intro x
    by_cases hall : ∀ θ, S.prob θ x = 0
    · simp only [hall, Finset.sum_const_zero]
      apply le_antisymm
      · exact ciSup_le (fun θ => (hall θ).le)
      · exact hml0 x
    · push Not at hall
      obtain ⟨θ0, h0⟩ := hall
      have hx0 : x ∈ supp θ0 := by
        by_contra hx
        exact h0 (hout θ0 x hx)
      have hzero : ∀ θ, θ ≠ θ0 → S.prob θ x = 0 := by
        intro θ hθ
        apply hout θ x
        intro hxθ
        exact Finset.disjoint_left.mp (hdisj θ θ0 hθ) hxθ hx0
      rw [Finset.sum_eq_single θ0 (fun θ _ hθ => hzero θ hθ) (by simp)]
      apply le_antisymm
      · refine ciSup_le (fun θ => ?_)
        by_cases hθ : θ = θ0
        · rw [hθ]
        · rw [hzero θ hθ]
          exact S.nonneg θ0 x
      · exact hle θ0 x
  unfold SourceClass.shtarkovSum
  simp only [hmlsum]
  rw [Finset.sum_comm]
  simp only [S.sum_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
