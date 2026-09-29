-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
-- name    : ErdosProblems_Erdos1049_QProductBoundsR10
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:45:16.886589+00:00
-- url     : https://prove2.me/theorems/ba1d5aed-58c1-41a9-acdf-093c4af69899
-- title:
--   Positive q-products and q-binomial ratio coefficients
-- statement:
--   An absolutely convergent logarithmic series constructs the positive infinite q-product as the limit of finite products and bounds the source positive series. The submitted module contains the source declarations summable_nonneg_dominated, abs_log_one_sub_le, qPochhammerFinite, qPochhammerFinite_zero, qPochhammerFinite_succ, among others. Source topic: Positive q-products and q-binomial ratio coefficients.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QProductBoundsR10.lean#L18-L282
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

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
namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped BigOperators Topology





noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)













noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))



























end ErdosProblems.Erdos1049.PaperR10


