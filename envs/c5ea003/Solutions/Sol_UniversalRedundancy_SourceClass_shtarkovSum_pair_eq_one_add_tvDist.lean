-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.shtarkovSum_pair_eq_one_add_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T16:54:30.18185+00:00
-- url     : https://prove2.me/submissions/9d447219-2e39-48eb-88b8-0192132a5f8d

import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
open UniversalRedundancy UniversalRedundancy.SourceClass in
theorem solution {X : Type*} [Fintype X] (S : SourceClass X Bool) :
    S.shtarkovSum = 1 + tvDist (S.prob true) (S.prob false) := by
  have hb : ∀ θ y, S.prob θ y ≤ 1 := by
    intro θ y
    rw [← S.sum_one θ]
    exact Finset.single_le_sum (f := fun y => S.prob θ y) (fun z _ => S.nonneg θ z) (Finset.mem_univ y)
  have hml : ∀ x, S.maxLik x = max (S.prob true x) (S.prob false x) := by
    intro x
    have hbdd : BddAbove (Set.range fun θ => S.prob θ x) := ⟨1, by rintro _ ⟨θ, rfl⟩; exact hb θ x⟩
    apply le_antisymm
    · refine ciSup_le (fun θ => ?_)
      cases θ
      · exact le_max_right _ _
      · exact le_max_left _ _
    · exact max_le (le_ciSup hbdd true) (le_ciSup hbdd false)
  have hmax : ∀ a b : ℝ, max a b = (a + b + |a - b|) / 2 := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
      ring
  unfold SourceClass.shtarkovSum tvDist
  simp only [hml, hmax]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, S.sum_one, S.sum_one]
  ring
