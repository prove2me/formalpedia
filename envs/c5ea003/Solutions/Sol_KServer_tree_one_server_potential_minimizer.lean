-- Prove2me | solution 1 for KServer.tree_one_server_potential_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T21:56:08.850882+00:00
-- url     : https://prove2.me/submissions/290e1c70-fc23-46ab-b043-b91c4fd63c29

import Mathlib
import Definitions.Def_KServer_tree_metric
import Theorems.Thm_KServer_tree_four_point

open KServer

/-- **Coester–Koutsoupias, Lemma 24**: on a tree, any minimizer of `w x - d c x`
realizes the one-server potential. -/
theorem solution (M : Type) [MetricSpace M] [Fintype M] (hM : IsTreeVertexSpace M)
    (w : M → ℝ) (Δ : ℝ) (c x : M) (hx : ∀ u : M, w x - dist c x ≤ w u - dist c u)
    (y z : M) :
    min (w x + w z + Δ - dist x z) (w x + w y + Δ - dist x y)
      ≤ w y + w z + Δ - dist y z := by
  have h4 := tree_four_point M hM c x y z
  have hy := hx y
  have hz := hx z
  rcases max_cases (dist c y + dist x z) (dist c z + dist x y) with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he] at h4
    refine le_trans (min_le_left _ _) ?_
    linarith
  · rw [he] at h4
    refine le_trans (min_le_right _ _) ?_
    linarith
