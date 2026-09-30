-- Prove2me | solution 1 for lean_workbook_plus_49513
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:26.012128+00:00
-- url     : https://prove2.me/submissions/65bf4d53-2f3c-4388-9125-0041e0784dc1

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz

theorem solution (f : ℝ → ℝ)
    (hf : ∀ x y : ℝ, abs (f x - f y) ≤ (1 / 2) * abs (x - y)) : Continuous f := by
  have hLip : LipschitzWith (Real.toNNReal (1 / 2)) f :=
    LipschitzWith.of_dist_le' (fun x y => by simpa only [Real.dist_eq] using hf x y)
  exact hLip.continuous

#print axioms solution
