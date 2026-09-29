-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.shtarkovSum_eq_card_iff_mutuallySingular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T16:46:04.517266+00:00
-- url     : https://prove2.me/submissions/c6eb7a89-c2c8-4c12-bdd7-6c393cf31f38

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Fintype Θ] [Nonempty Θ] :
    S.shtarkovSum = (Fintype.card Θ : ℝ) ↔ S.MutuallySingular := by
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
  have hiff : S.shtarkovSum = (Fintype.card Θ : ℝ) ↔ S.MutuallySingular := by
    have hsumle : ∀ x, S.maxLik x ≤ ∑ θ, S.prob θ x := by
      intro x
      obtain ⟨θs, hθs⟩ := exists_eq_ciSup_of_finite (f := fun θ => S.prob θ x)
      have hm : S.maxLik x = S.prob θs x := hθs.symm
      rw [hm]
      exact Finset.single_le_sum (f := fun θ => S.prob θ x) (fun θ _ => S.nonneg θ x) (Finset.mem_univ θs)
    have htot : ∑ x, ∑ θ, S.prob θ x = (Fintype.card Θ : ℝ) := by
      rw [Finset.sum_comm]
      simp only [S.sum_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    constructor
    · intro hC x θ θ' hne
      have hpt : ∀ x, S.maxLik x = ∑ θ, S.prob θ x := by
        have h : ∑ x, S.maxLik x = ∑ x, ∑ θ, S.prob θ x := by
          rw [htot]
          exact hC
        exact fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => hsumle x)).mp h x (Finset.mem_univ x)
      obtain ⟨θs, hθs⟩ := exists_eq_ciSup_of_finite (f := fun θ => S.prob θ x)
      have hm : S.maxLik x = S.prob θs x := hθs.symm
      by_contra hc
      push Not at hc
      have hp1 : 0 < S.prob θ x := lt_of_le_of_ne (S.nonneg θ x) (Ne.symm hc.1)
      have hp2 : 0 < S.prob θ' x := lt_of_le_of_ne (S.nonneg θ' x) (Ne.symm hc.2)
      obtain ⟨θ'', hne'', hp''⟩ : ∃ θ'', θ'' ≠ θs ∧ 0 < S.prob θ'' x := by
        by_cases hθ : θ = θs
        · exact ⟨θ', fun h' => hne (hθ.trans h'.symm), hp2⟩
        · exact ⟨θ, hθ, hp1⟩
      have hsum : S.prob θs x + S.prob θ'' x ≤ ∑ θ, S.prob θ x := by
        classical
        have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {θs, θ''})
          (fun i _ _ => S.nonneg i x) (f := fun θ => S.prob θ x)
        rwa [Finset.sum_pair hne''.symm] at this
      have := hpt x
      linarith
    · intro hsing
      have hmlsum : ∀ x, S.maxLik x = ∑ θ, S.prob θ x := by
        intro x
        by_cases hall : ∀ θ, S.prob θ x = 0
        · simp only [hall, Finset.sum_const_zero]
          apply le_antisymm
          · exact ciSup_le (fun θ => (hall θ).le)
          · exact hml0 x
        · push Not at hall
          obtain ⟨θ0, h0⟩ := hall
          have hzero : ∀ θ, θ ≠ θ0 → S.prob θ x = 0 := fun θ hθ => (hsing x θ θ0 hθ).resolve_right h0
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
      exact htot
  exact hiff
