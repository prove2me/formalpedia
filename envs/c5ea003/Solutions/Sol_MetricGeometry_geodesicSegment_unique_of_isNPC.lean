-- Prove2me | solution 1 for MetricGeometry.geodesicSegment_unique_of_isNPC
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T21:21:01.829562+00:00
-- url     : https://prove2.me/submissions/5913e025-c96e-4bb2-b587-9eec00f28a2f

import Definitions.Def_metric_geodesic_angle
import Theorems.Thm_MetricGeometry_dist_midpoint_le_of_isNPC

open MetricGeometry InnerProductGeometry

theorem solution {X : Type*} [MetricSpace X] (hnpc : IsNPC X) (hmid : HasMidpoints X)
    (g1 g2 : ℝ → X) (x y : X) (h1 : IsGeodesicSegment g1 x y)
    (h2 : IsGeodesicSegment g2 x y) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    g1 t = g2 t := by
  obtain ⟨h10, h11, h1d⟩ := h1
  obtain ⟨h20, h21, h2d⟩ := h2
  obtain ⟨ht0, ht1⟩ := ht
  have hD : (0 : ℝ) ≤ dist x y := dist_nonneg
  have e1 : dist (g1 t) x = t * dist x y := by
    have h := h1d 0 (by norm_num) t ⟨ht0, ht1⟩
    rw [h10, dist_comm] at h
    rw [h, abs_of_nonpos (by linarith)]; ring
  have e2 : dist (g1 t) y = (1 - t) * dist x y := by
    have h := h1d t ⟨ht0, ht1⟩ 1 (by norm_num)
    rw [h11] at h
    rw [h, abs_of_nonpos (by linarith)]; ring
  have e3 : dist (g2 t) x = t * dist x y := by
    have h := h2d 0 (by norm_num) t ⟨ht0, ht1⟩
    rw [h20, dist_comm] at h
    rw [h, abs_of_nonpos (by linarith)]; ring
  have e4 : dist (g2 t) y = (1 - t) * dist x y := by
    have h := h2d t ⟨ht0, ht1⟩ 1 (by norm_num)
    rw [h21] at h
    rw [h, abs_of_nonpos (by linarith)]; ring
  obtain ⟨m, hm⟩ := hmid (g1 t) (g2 t)
  have hmx : dist m x ≤ t * dist x y := by
    have := MetricGeometry.dist_midpoint_le_of_isNPC hnpc (g1 t) (g2 t) m x hm
    rw [e1, e3] at this; linarith
  have hmy : dist m y ≤ (1 - t) * dist x y := by
    have := MetricGeometry.dist_midpoint_le_of_isNPC hnpc (g1 t) (g2 t) m y hm
    rw [e2, e4] at this; linarith
  have htri : dist x y ≤ dist x m + dist m y := dist_triangle x m y
  have hxm : dist x m = dist m x := dist_comm x m
  have hmxeq : dist m x = t * dist x y := by linarith
  have hcn := hnpc (g1 t) (g2 t) m x hm
  rw [e1, e3, hmxeq] at hcn
  have hd : (0 : ℝ) ≤ dist (g1 t) (g2 t) := dist_nonneg
  have : dist (g1 t) (g2 t) = 0 := by nlinarith [hcn, hd]
  exact dist_eq_zero.mp this
