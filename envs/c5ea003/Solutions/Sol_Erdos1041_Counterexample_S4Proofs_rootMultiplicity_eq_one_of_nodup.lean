-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.rootMultiplicity_eq_one_of_nodup
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:28:02.660114+00:00
-- url     : https://prove2.me/submissions/bfcc59e5-9df0-417a-8d66-d92c1882a8bb

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution {p : Polynomial ℂ} (hp : p ≠ 0)
    (hnd : p.roots.Nodup) {z : ℂ} (hz : p.IsRoot z) :
    Polynomial.rootMultiplicity z p = 1 := by
  have hmem : z ∈ p.roots := (Polynomial.mem_roots hp).mpr hz
  rw [← Polynomial.count_roots]
  exact Multiset.count_eq_one_of_mem hnd hmem
