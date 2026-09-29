-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.hasSum_qPochhammer_log_majorant
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:56:14.706316+00:00
-- url     : https://prove2.me/submissions/a2e22cd2-2b7a-4470-b263-8f40f08c6bd9

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
theorem solution {a q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => a * q ^ k / (1 - a))
      (a / ((1 - a) * (1 - q))) := by
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (a / (1 - a))
  convert h using 1 <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
