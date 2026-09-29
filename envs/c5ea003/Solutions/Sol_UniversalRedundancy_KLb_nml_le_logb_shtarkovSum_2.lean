-- Prove2me | solution 2 for UniversalRedundancy.KLb_nml_le_logb_shtarkovSum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:59:08.762203+00:00
-- url     : https://prove2.me/submissions/3edd004d-36fd-4187-a160-cdc5711cc945

import Definitions.Def_MachineLearning_UniversalRedundancy_Capacity
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] {Θ : Type*} [Nonempty Θ] (S : SourceClass X Θ)
    (θ : Θ) (hp : ∀ θ x, 0 < S.prob θ x) (hmax : ∀ x, 0 < S.maxLik x) :
    KLb (S.prob θ) S.nml ≤ Real.logb 2 S.shtarkovSum := by
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
  unfold KLb
  calc ∑ x, S.prob θ x * Real.logb 2 (S.prob θ x / S.nml x)
      ≤ ∑ x, S.prob θ x * Real.logb 2 S.shtarkovSum := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        apply mul_le_mul_of_nonneg_left _ (S.nonneg θ x)
        have hnml : 0 < S.nml x := div_pos (hmax x) hCpos
        apply Real.logb_le_logb_of_le (by norm_num) (div_pos (hp θ x) hnml)
        rw [div_le_iff₀ hnml]
        unfold SourceClass.nml
        rw [mul_div_assoc', le_div_iff₀ hCpos]
        nlinarith [hle θ x, hCpos]
    _ = Real.logb 2 S.shtarkovSum := by
        rw [← Finset.sum_mul, S.sum_one θ, one_mul]
