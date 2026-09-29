-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_summable_nonneg_dominated
-- name    : ErdosProblems.Erdos1049.PaperR10.summable_nonneg_dominated
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:09:17.233098+00:00
-- url     : https://prove2.me/theorems/cf9962a4-35b8-4ca9-ad10-9be55fe6dbbf
-- title:
--   Summable nonneg dominated
-- statement:
--   If real sequences f,g satisfy 0≤f(k)≤g(k) for every natural k and g is summable, then f is summable.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QProductBoundsR10.lean#L18-L25
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

theorem ErdosProblems.Erdos1049.PaperR10.summable_nonneg_dominated {f g : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hfg : ∀ k, f k ≤ g k) (hg : Summable g) : Summable f := by sorry
