-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.shtarkov_minimax
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:43:43.496716+00:00
-- url     : https://prove2.me/submissions/de78c86e-8721-428b-ac9c-4e076064462a

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ] :
    (∀ θ x, S.prob θ x ≤ S.shtarkovSum * S.nml x) ∧
      (∀ q : X → ℝ, (∀ x, 0 ≤ q x) → ∑ x, q x ≤ 1 →
        ∀ c : ℝ, (∀ θ x, S.prob θ x ≤ c * q x) → S.shtarkovSum ≤ c) := by
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
  refine ⟨fun θ x => ?_, fun q hq0 hq1 c hc => ?_⟩
  · have h : S.shtarkovSum * S.nml x = S.maxLik x := by
      unfold SourceClass.nml
      field_simp
    rw [h]
    exact hle θ x
  · have hml : ∀ x, S.maxLik x ≤ c * q x := fun x => ciSup_le (fun θ => hc θ x)
    have hsum : S.shtarkovSum ≤ c * ∑ x, q x := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun x _ => hml x)
    have hq : 0 ≤ ∑ x, q x := Finset.sum_nonneg (fun x _ => hq0 x)
    by_cases hc0 : 0 ≤ c
    · nlinarith
    · push Not at hc0
      nlinarith
