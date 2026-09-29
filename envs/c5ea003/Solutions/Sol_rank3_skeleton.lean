-- Prove2me | solution 1 for rank3_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:48:51.035034+00:00
-- url     : https://prove2.me/submissions/2687e596-6024-429e-af2e-696b1bb7cec2

import Mathlib
import Definitions.Def_Bridges_Skeleton
import Definitions.Def_Bridges_TropicalHecke_MinPlusAlgebra
open Set MinPlusExpr in
theorem solution :
    BuildingSkeleton rank3_weyl = {v : Fin 3 → ℝ | v 0 = 0 ∧ v 1 + v 1 ≤ v 0 + v 2} := by
  ext v
  simp only [BuildingSkeleton, rank3_weyl, normalizedTropRelationLocus, tropRelationLocus,
    NormalizedVectors, mem_inter_iff, mem_setOf_eq, List.mem_singleton, forall_eq,
    TropRelation.satisfiedAt, MinPlusExpr.eval]
  -- `min (v₀ + v₂) (2 v₁) = 2 v₁ ↔ 2 v₁ ≤ v₀ + v₂`
  rw [min_eq_right_iff]
  exact and_comm
