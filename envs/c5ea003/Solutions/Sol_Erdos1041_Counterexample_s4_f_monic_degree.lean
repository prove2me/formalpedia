-- Prove2me | solution 1 for Erdos1041.Counterexample.s4_f_monic_degree
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:32:59.870991+00:00
-- url     : https://prove2.me/submissions/089df834-896f-4119-a3a7-9de46b98713d

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

section
noncomputable section
open scoped ComplexConjugate NNReal
namespace Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
theorem s4_f_monic_degree' : f.Monic ∧ f.natDegree = 7 := by
  constructor
  · unfold f
    monicity!
  · unfold f
    compute_degree!
end Erdos1041.Counterexample.S4Proofs
end
end

noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution : f.Monic ∧ f.natDegree = 7 :=
  S4Proofs.s4_f_monic_degree'
