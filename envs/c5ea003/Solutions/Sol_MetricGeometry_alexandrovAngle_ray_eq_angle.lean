-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_ray_eq_angle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T22:53:08.040666+00:00
-- url     : https://prove2.me/submissions/5107d610-a73a-4ed2-8781-60cabed43fe3

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_eq_angle

open MetricGeometry Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p u v : E) :
    alexandrovAngle p (fun t => p + t • u) (fun t => p + t • v)
      = InnerProductGeometry.angle u v := by
  have key : ∀ (g1 g2 : ℝ → E) (c : ℝ),
      (∀ s t : ℝ, 0 < s → 0 < t → comparisonAngle p (g1 s) (g2 t) = c) →
      alexandrovAngle p g1 g2 = c := by
    intro g1 g2 c h
    have h1 : ∀ᶠ s in 𝓝[>] (0:ℝ), (0:ℝ) < s := eventually_mem_nhdsWithin
    have hev : ∀ᶠ st in ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))),
        comparisonAngle p (g1 st.1) (g2 st.2) = c :=
      (h1.prod_mk h1).mono (fun st hst => h _ _ hst.1 hst.2)
    rw [alexandrovAngle, limsup_congr hev, limsup_const]
  refine key _ _ _ (fun s t hs ht => ?_)
  rw [comparisonAngle_eq_angle]
  simp only [add_sub_cancel_left]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]
