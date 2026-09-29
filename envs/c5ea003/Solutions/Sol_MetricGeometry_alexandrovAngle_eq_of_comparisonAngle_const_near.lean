-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_eq_of_comparisonAngle_const_near
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:01:05.34195+00:00
-- url     : https://prove2.me/submissions/9fa7e4e8-5b62-4266-bf4c-303c81550e03

import Definitions.Def_metric_alexandrov_angle

open MetricGeometry Filter

universe u

theorem solution {X : Type u} [PseudoMetricSpace X]
    (p : X) (g1 g2 : ℝ → X) (c eps : ℝ) (heps : 0 < eps)
    (h : ∀ s t : ℝ, 0 < s → s < eps → 0 < t → t < eps →
      comparisonAngle p (g1 s) (g2 t) = c) :
    alexandrovAngle p g1 g2 = c := by
  have h1 : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < s ∧ s < eps := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds heps)]
      with s hs1 hs2
    exact ⟨hs1, hs2⟩
  have hev : ∀ᶠ st in (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhdsWithin (0 : ℝ) (Set.Ioi 0)),
      comparisonAngle p (g1 st.1) (g2 st.2) = c := by
    rw [Filter.eventually_prod_iff]
    exact ⟨fun s => 0 < s ∧ s < eps, h1, fun t => 0 < t ∧ t < eps, h1,
      fun {s} hs {t} ht => h s t hs.1 hs.2 ht.1 ht.2⟩
  unfold alexandrovAngle
  rw [Filter.limsup_congr hev]
  exact Filter.limsup_const c
