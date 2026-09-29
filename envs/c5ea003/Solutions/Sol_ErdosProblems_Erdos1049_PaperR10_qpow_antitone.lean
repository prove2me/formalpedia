-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.qpow_antitone
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:51:22.532229+00:00
-- url     : https://prove2.me/submissions/35e7bcb5-d825-4d55-b1d1-50c2c6a882d1

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
theorem solution {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {i j : ℕ} (hij : i ≤ j) : q ^ j ≤ q ^ i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add]
  simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (pow_nonneg hq0 i)
