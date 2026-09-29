-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.physicalRoot_injective
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:23:48.451751+00:00
-- url     : https://prove2.me/submissions/517367ef-b670-4910-b077-de32b8c2ecc4

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_cayley_den_ne_zero
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_ne_zero
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_realRoot_mem
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
theorem cayley_injective : Function.Injective cayley := by
  intro x y h
  have hc := (div_eq_div_iff (cayley_den_ne_zero x) (cayley_den_ne_zero y)).mp h
  have hi := congrArg Complex.im hc
  norm_num at hi
  linarith
theorem realRoot_injective : Function.Injective realRoot := by
  intro i j hij
  by_contra hne
  have hi := realRoot_mem i
  have hj := realRoot_mem j
  fin_cases i <;> fin_cases j <;>
    norm_num [Set.mem_Ioo, bracketLo, bracketHi] at * <;> linarith
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : Function.Injective physicalRoot := by
  intro i j h
  apply realRoot_injective
  apply cayley_injective
  exact mul_left_cancel₀ rho_ne_zero h
