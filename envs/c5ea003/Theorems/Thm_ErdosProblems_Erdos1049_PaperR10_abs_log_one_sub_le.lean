-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_abs_log_one_sub_le
-- name    : ErdosProblems.Erdos1049.PaperR10.abs_log_one_sub_le
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:55:22.046224+00:00
-- url     : https://prove2.me/theorems/4f4239f8-63fc-4350-9a30-2d03800528de
-- title:
--   Abs log one sub le
-- statement:
--   For real 0≤u≤a<1, the logarithmic bound |log(1−u)|≤u/(1−a) holds.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QProductBoundsR10.lean#L27-L45
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Positive q-products and q-binomial ratio coefficients

The infinite product is constructed from an absolutely
convergent logarithmic series, and is proved to be the limit of its finite
products. Its positivity is therefore not an assumed supplier.
-/
open Filter
open scoped BigOperators Topology

open ErdosProblems.Erdos1049.PaperR10

theorem ErdosProblems.Erdos1049.PaperR10.abs_log_one_sub_le {u a : ℝ}
    (hu : 0 ≤ u) (hua : u ≤ a) (ha : a < 1) :
    |Real.log (1 - u)| ≤ u / (1 - a) := by sorry
