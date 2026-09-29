-- Prove2me | solution 1 for ConvexOptimization.smul_mem_dualCone
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T04:48:19.334518+00:00
-- url     : https://prove2.me/submissions/9f6dcc43-2e1e-4795-a674-364a05341a0a

import Mathlib
import Definitions.Def_dualCone

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem solution {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ dualCone K) (c : ℝ) (hc : 0 ≤ c) :
    c • z ∈ dualCone K := by
  intro x hx
  rw [real_inner_smul_right]
  exact mul_nonneg hc (hz x hx)
