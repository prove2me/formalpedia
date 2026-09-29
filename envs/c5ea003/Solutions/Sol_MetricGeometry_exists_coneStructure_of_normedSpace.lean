-- Prove2me | solution 1 for MetricGeometry.exists_coneStructure_of_normedSpace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T18:32:31.594982+00:00
-- url     : https://prove2.me/submissions/38d924c9-7526-43ac-8c3f-e60f7f720566

import Definitions.Def_metric_npc_cone

open MetricGeometry

theorem solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ K : ConeStructure E, K.vertex = 0 ∧
      ∀ (lam : ℝ) (p : E), K.scale lam p = lam • p := by
  refine ⟨⟨0, fun lam p => lam • p, ?_, ?_, ?_, ?_⟩, rfl, fun _ _ => rfl⟩
  · intro lam hlam p q
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam, dist_eq_norm]
  · intro p; simp
  · intro p; simp
  · intro a b _ _ p; exact smul_smul a b p
