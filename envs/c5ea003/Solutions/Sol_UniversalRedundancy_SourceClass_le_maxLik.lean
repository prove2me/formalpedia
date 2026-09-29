-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.le_maxLik
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T16:46:24.737218+00:00
-- url     : https://prove2.me/submissions/d7ef4362-c33c-4849-aa98-1c015c98aed0

import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core

open UniversalRedundancy

theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)
    (θ : Θ) (x : X) : S.prob θ x ≤ S.maxLik x := by
  change S.prob θ x ≤ ⨆ θ' : Θ, S.prob θ' x
  refine le_ciSup (f := fun θ' : Θ => S.prob θ' x) ?_ θ
  refine ⟨(1 : ℝ), ?_⟩
  rintro _ ⟨θ', rfl⟩
  have hsum := S.sum_one θ'
  calc
    S.prob θ' x ≤ ∑ y, S.prob θ' y :=
      Finset.single_le_sum (fun y _ => S.nonneg θ' y) (Finset.mem_univ x)
    _ = 1 := hsum
