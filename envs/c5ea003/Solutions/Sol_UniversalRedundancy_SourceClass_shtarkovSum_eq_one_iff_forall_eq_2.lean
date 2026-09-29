-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.shtarkovSum_eq_one_iff_forall_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:23:56.042691+00:00
-- url     : https://prove2.me/submissions/bab2a8a2-276e-4a2e-9a53-6acaf0a0ab67

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ] :
    S.shtarkovSum = 1 ↔ ∀ θ θ' x, S.prob θ x = S.prob θ' x := by
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
  constructor
  · intro hC
    have heq : ∀ θ x, S.prob θ x = S.maxLik x := by
      intro θ x
      have hsum : ∑ y, S.prob θ y = ∑ y, S.maxLik y := by
        rw [S.sum_one θ]
        exact hC.symm
      exact (Finset.sum_eq_sum_iff_of_le (fun y _ => hle θ y)).mp hsum x (Finset.mem_univ x)
    intro θ θ' x
    rw [heq θ x, heq θ' x]
  · intro hone
    obtain ⟨θ₀⟩ := ‹Nonempty Θ›
    have hml : ∀ x, S.maxLik x = S.prob θ₀ x := by
      intro x
      apply le_antisymm
      · exact ciSup_le (fun θ => (hone θ θ₀ x).le)
      · exact hle θ₀ x
    simp only [SourceClass.shtarkovSum, hml]
    exact S.sum_one θ₀
