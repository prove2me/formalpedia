-- Prove2me | solution 1 for lean_workbook_plus_3721
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:23.091106+00:00
-- url     : https://prove2.me/submissions/94f228f3-476f-4118-822d-1af3f923b186

import Mathlib.Topology.MetricSpace.Lipschitz

theorem solution (X : Type*) [MetricSpace X]
    (α : ℝ) (hα : 0 < α ∧ α < 1) (f : X → X)
    (hf : ∀ x y, dist (f x) (f y) ≤ α * dist x y) :
    Continuous (fun x => dist (f x) x) := by
  have hLip : LipschitzWith (Real.toNNReal α) f := LipschitzWith.of_dist_le' hf
  exact hLip.continuous.dist continuous_id

#print axioms solution
