-- Prove2me | solution 1 for mme_released_recursive_level3_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:25:24.062997+00:00
-- url     : https://prove2.me/submissions/814445ed-d710-4002-a7ff-65d46cd20941

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters

open BigOperators MME MME.RecursiveYZ MME.RecStage
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


namespace MME.L3Bnd

/-- Every tabulated level-three cell has its free parameter below half the scale. -/
theorem cells_le : ∀ (ρ : Fin 6) (r : Fin 88), ∀ x ∈ cellsAt ρ r, 2 * x.2.2 ≤ D := by
  decide +kernel

/-- Hence every cell reached by the lookup does. -/
theorem cellRec_le (ρ : Fin 6) (r : Fin 88)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r)) :
    2 * (cellRec ρ r c).2 ≤ D := by
  classical
  unfold cellRec
  split
  · rename_i x h
    exact cells_le ρ r x (List.mem_of_find?_eq_some h)
  · norm_num


end MME.L3Bnd

theorem solution :
    (∀ (ρ : Fin 6) (r : Fin 88), ∀ x ∈ cellsAt ρ r, 2 * x.2.2 ≤ D) ∧
    ∀ (ρ : Fin 6) (r : Fin 88)
      (c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r)),
      2 * (cellRec ρ r c).2 ≤ D :=
  ⟨MME.L3Bnd.cells_le, MME.L3Bnd.cellRec_le⟩
