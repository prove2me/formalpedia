-- Prove2me | Theorems.Thm_TopologicalSpace_NonemptyCompacts_convex_of_tendsto
-- name    : TopologicalSpace.NonemptyCompacts.convex_of_tendsto
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T18:06:26.524049+00:00
-- url     : https://prove2.me/theorems/83d0d5dc-0a7a-4680-8b0b-f40c3e093274
-- title:
--   Hausdorff limits of compact convex sets are convex
-- statement:
--   Approximate points from each set, pass convex combinations to the limit via infDist continuity. Drift: Metric.lipschitz_infDist_set / uniformContinuous_infDist_Hausdorff_dist for newer NonemptyCompacts APIs; nhds for N.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Convex/Hausdorff.lean#L10-L14

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Sequences
open Filter TopologicalSpace
open scoped Topology

namespace TopologicalSpace.NonemptyCompacts

theorem convex_of_tendsto {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} [l.NeBot] {K : ι → NonemptyCompacts E} {L : NonemptyCompacts E}
    (hK : ∀ n, Convex ℝ (K n : Set E)) (hlim : Tendsto K l (nhds L)) :
    Convex ℝ (L : Set E) := by sorry

end TopologicalSpace.NonemptyCompacts
