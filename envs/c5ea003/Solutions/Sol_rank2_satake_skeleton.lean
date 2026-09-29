-- Prove2me | solution 1 for rank2_satake_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:30:27.06115+00:00
-- url     : https://prove2.me/submissions/97b5384e-dcbd-400c-9be5-d01dd09912ef

import Mathlib
import Definitions.Def_Bridges_Skeleton
import Definitions.Def_Bridges_TropicalHecke_MinPlusAlgebra
open MinPlusExpr in
theorem solution : BuildingSkeleton rank2_satake = {v : Fin 2 → ℝ | v 0 = 0 ∧ v 1 ≤ 0} := by
  ext v
  -- the single relation `min(x₀, x₁) = x₁` says `x₁ ≤ x₀`, and normalisation says `x₀ = 0`
  simp only [BuildingSkeleton, normalizedTropRelationLocus, tropRelationLocus, NormalizedVectors,
    rank2_satake, Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_singleton, forall_eq,
    TropRelation.satisfiedAt, MinPlusExpr.eval]
  constructor
  · rintro ⟨h1, h0⟩
    refine ⟨h0, ?_⟩
    rw [← h0]
    exact min_eq_right_iff.mp h1
  · rintro ⟨h0, h1⟩
    refine ⟨min_eq_right (h0 ▸ h1), h0⟩
