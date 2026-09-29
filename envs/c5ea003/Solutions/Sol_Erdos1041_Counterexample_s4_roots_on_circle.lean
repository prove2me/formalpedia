-- Prove2me | solution 1 for Erdos1041.Counterexample.s4_roots_on_circle
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:33:50.086975+00:00
-- url     : https://prove2.me/submissions/36fc4100-3ea9-46b4-b282-212dcb116f9b

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_f_ne_zero
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_f_roots_eq
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_physicalRoot_norm
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
/-- The second obligation. -/
theorem s4_roots_on_circle' : ∀ z, f.IsRoot z → ‖z‖ = (ρ : ℝ) := by
  intro z hz
  have hm : z ∈ rootMul := by
    rw [← f_roots_eq]
    exact (Polynomial.mem_roots f_ne_zero).mpr hz
  obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hm
  exact physicalRoot_norm j
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
theorem solution : ∀ z, f.IsRoot z → ‖z‖ = (ρ : ℝ) :=
  S4Proofs.s4_roots_on_circle'
