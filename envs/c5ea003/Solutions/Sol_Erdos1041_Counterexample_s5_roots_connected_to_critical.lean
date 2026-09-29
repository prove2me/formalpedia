-- Prove2me | solution 1 for Erdos1041.Counterexample.s5_roots_connected_to_critical
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:43:43.704974+00:00
-- url     : https://prove2.me/submissions/6e609f37-44be-451e-b7af-1cf2832da5d3

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_endpoint3
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_endpoint6
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_joined_zs_wq
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_s5_of_endpoint_joins
import Theorems.Thm_Erdos1041_Counterexample_s4_instance_critical
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open scoped ComplexConjugate

namespace Erdos1041.Counterexample
/-- Owned by slice S4: the uniqueness and localisation conjuncts of `s4_instance_critical`
give this immediately (apply global uniqueness to `zs`, then read off the localisation of the
distinguished critical point). S5 consumes it; it is not S5's to prove. -/
theorem s4_zs_localisation (zs : ℂ) (hzs : zs ∈ Omega f)
    (hcrit : (Polynomial.derivative f).IsRoot zs) :
    ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000 := by
  obtain ⟨zs', _, _, _, _, _, _, _, huniq, _, _, _, _, _, _, _, _, hloc, _⟩ := s4_instance_critical
  have hzs' : zs = zs' := huniq zs hzs hcrit
  rw [hzs']
  exact hloc
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution
    (zs b₃ b₆ : ℂ) (hzs : zs ∈ Omega f)
    (hcrit : (Polynomial.derivative f).IsRoot zs)
    (hr₃ : f.IsRoot b₃) (hr₆ : f.IsRoot b₆)
    (hnear₃ : ‖b₃ - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10)
    (hnear₆ : ‖b₆ - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10) :
    b₃ ∈ connectedComponentIn (Omega f) zs ∧ b₆ ∈ connectedComponentIn (Omega f) zs :=
  InstanceConnectivity.s5_of_endpoint_joins zs b₃ b₆
    (InstanceConnectivity.joined_zs_wq zs hcrit (s4_zs_localisation zs hzs hcrit))
    (InstanceConnectivity.endpoint3 b₃ hr₃ hnear₃)
    (InstanceConnectivity.endpoint6 b₆ hr₆ hnear₆)
