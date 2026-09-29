-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.summable_nonneg_dominated
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:09:51.787984+00:00
-- url     : https://prove2.me/submissions/1f55646e-5310-4045-aeae-0a945c388cf1

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

namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped BigOperators Topology
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution {f g : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hfg : ∀ k, f k ≤ g k) (hg : Summable g) : Summable f := by
  apply summable_of_sum_le hf
  intro s
  exact (Finset.sum_le_sum (fun k _ => hfg k)).trans
    (hg.sum_le_tsum s (fun k _ => (hf k).trans (hfg k)))
