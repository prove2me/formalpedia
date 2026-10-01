-- Prove2me | solution 1 for ConvexBody.mem_of_tendsto_hausdorffDist
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:53:48.267207+00:00
-- url     : https://prove2.me/submissions/5561b8ca-4558-42e0-b824-ef3813bae575

import Mathlib.Analysis.Convex.Body
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

open Filter
open scoped Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E) (K : ℕ → ConvexBody E) (L : ConvexBody E)
    (hev : Filter.Eventually (fun n => q ∈ (K n : Set E)) atTop)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E))
      atTop (nhds 0)) : q ∈ (L : Set E) := by
  have hle : Filter.EventuallyLE atTop (fun _ : ℕ ↦ Metric.infDist q (L : Set E))
      (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E)) := by
    filter_upwards [hev] with n hn
    exact Metric.infDist_le_hausdorffDist_of_mem hn
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
  have hz : Metric.infDist q (L : Set E) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  exact (IsClosed.mem_iff_infDist_zero L.isClosed L.nonempty).mpr
    (le_antisymm hz Metric.infDist_nonneg)
