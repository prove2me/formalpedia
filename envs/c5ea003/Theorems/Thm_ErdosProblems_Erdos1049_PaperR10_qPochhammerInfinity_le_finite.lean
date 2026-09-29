-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_qPochhammerInfinity_le_finite
-- name    : ErdosProblems.Erdos1049.PaperR10.qPochhammerInfinity_le_finite
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:57:26.384205+00:00
-- url     : https://prove2.me/theorems/af3ad7e0-0b84-48de-ad3f-a572300bc9ab
-- title:
--   Q pochhammer infinity le finite
-- statement:
--   For real 0≤a<1 and 0≤q<1, the source-defined infinite q-Pochhammer product is no greater than any finite prefix qPochhammerFinite(a,q,n).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QProductBoundsR10.lean#L139-L161
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

theorem ErdosProblems.Erdos1049.PaperR10.qPochhammerInfinity_le_finite {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    qPochhammerInfinity a q ≤ qPochhammerFinite a q n := by sorry
