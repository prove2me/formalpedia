-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_eq_zero_trans
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T01:34:57.226854+00:00
-- url     : https://prove2.me/submissions/8503d31c-d601-48a6-bdb3-fcb59400f611

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_alexandrovAngle_comm
import Theorems.Thm_MetricGeometry_alexandrovAngle_mem_Icc
import Theorems.Thm_MetricGeometry_alexandrovAngle_triangle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p : X) (c c' c'' : ℝ → X)
    (a : ℝ) (ha : 0 < a)
    (hc : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c t) = t)
    (hc' : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c' t) = t)
    (hc'' : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c'' t) = t)
    (h1 : alexandrovAngle p c c' = 0) (h2 : alexandrovAngle p c' c'' = 0) :
    alexandrovAngle p c c'' = 0 := by
  have htri := MetricGeometry.alexandrovAngle_triangle p c' c c'' a ha hc' hc hc''
  rw [MetricGeometry.alexandrovAngle_comm p c' c] at htri
  have hle : alexandrovAngle p c c'' ≤ 0 := by rw [h1, h2] at htri; linarith
  exact le_antisymm hle (MetricGeometry.alexandrovAngle_mem_Icc p c c'').1
