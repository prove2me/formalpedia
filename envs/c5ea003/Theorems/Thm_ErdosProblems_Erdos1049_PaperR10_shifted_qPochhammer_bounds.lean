-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_shifted_qPochhammer_bounds
-- name    : ErdosProblems.Erdos1049.PaperR10.shifted_qPochhammer_bounds
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:57:40.255201+00:00
-- url     : https://prove2.me/theorems/4dc24697-018a-4b0b-8dab-5e6366d951d8
-- title:
--   Shifted q pochhammer bounds
-- statement:
--   For 0<q<1, natural n and positive natural s, the finite product qPochhammerFinite(qˢ,q,n) lies between qPochhammerInfinity(q,q) and 1.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QProductBoundsR10.lean#L192-L210
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

theorem ErdosProblems.Erdos1049.PaperR10.shifted_qPochhammer_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (s n : ℕ) (hs : 1 ≤ s) :
    qPochhammerInfinity q q ≤ qPochhammerFinite (q ^ s) q n ∧
      qPochhammerFinite (q ^ s) q n ≤ 1 := by sorry
