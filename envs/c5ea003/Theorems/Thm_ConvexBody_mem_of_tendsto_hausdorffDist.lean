-- Prove2me | Theorems.Thm_ConvexBody_mem_of_tendsto_hausdorffDist
-- name    : ConvexBody.mem_of_tendsto_hausdorffDist
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:53:42.13109+00:00
-- url     : https://prove2.me/theorems/a833b07e-35a6-47ca-900b-732b0547189a
-- title:
--   Hausdorff limits retain eventual members
-- statement:
--   If $q$ lies in $K_n$ eventually and the Hausdorff distance goes to $0$, then $q$ is in $L$. ASCII Eventually/nhds form.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Convex/Body/Hausdorff.lean#L12-L15

import Mathlib.Analysis.Convex.Body
import Mathlib.Topology.MetricSpace.HausdorffDistance
open Filter
open scoped Topology

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_of_tendsto_hausdorffDist (q : E) (K : ℕ → ConvexBody E) (L : ConvexBody E)
    (hev : Filter.Eventually (fun n => q ∈ (K n : Set E)) atTop)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E))
      atTop (nhds 0)) : q ∈ (L : Set E) := by sorry

end ConvexBody
