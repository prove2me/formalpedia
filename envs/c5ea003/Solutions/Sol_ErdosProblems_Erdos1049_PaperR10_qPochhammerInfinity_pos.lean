-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.qPochhammerInfinity_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:49:28.460503+00:00
-- url     : https://prove2.me/submissions/3c579c57-903d-422a-80f3-cbbd8102cbbb

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
theorem solution (a q : ℝ) : 0 < qPochhammerInfinity a q :=
  Real.exp_pos _
