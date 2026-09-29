-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.prob_le_shtarkovSum_mul_nml
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:19:51.317037+00:00
-- url     : https://prove2.me/submissions/e8aeb7f7-1731-4460-8474-b97c950b1c34

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ]
    (θ : Θ) (x : X) : S.prob θ x ≤ S.shtarkovSum * S.nml x := by
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
  have h : S.shtarkovSum * S.nml x = S.maxLik x := by
    unfold SourceClass.nml
    field_simp
  rw [h]
  exact hle θ x
