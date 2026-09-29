-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_qpow_antitone
-- name    : ErdosProblems.Erdos1049.PaperR10.qpow_antitone
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:51:09.989683+00:00
-- url     : https://prove2.me/theorems/080367b9-f819-4091-9feb-a030580d02e7
-- title:
--   Qpow antitone
-- statement:
--   For 0≤q≤1 and natural exponents i≤j, qʲ≤qⁱ.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QProductBoundsR10.lean#L185-L190
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

theorem ErdosProblems.Erdos1049.PaperR10.qpow_antitone {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {i j : ℕ} (hij : i ≤ j) : q ^ j ≤ q ^ i := by sorry
