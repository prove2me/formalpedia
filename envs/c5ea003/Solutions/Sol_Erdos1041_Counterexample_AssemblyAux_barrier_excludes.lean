-- Prove2me | solution 1 for Erdos1041.Counterexample.AssemblyAux.barrier_excludes
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:18:23.3551+00:00
-- url     : https://prove2.me/submissions/f0f43781-eb01-4995-ba23-9a57f9904db2

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Mathlib
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

namespace Erdos1041.Counterexample.AssemblyAux
end Erdos1041.Counterexample.AssemblyAux

noncomputable section
open scoped ComplexConjugate ENNReal

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.AssemblyAux
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.AssemblyAux in
theorem solution (p : Polynomial ℂ) (zs w : ℂ)
    (hzs : zs ∈ Omega p) (hw : w ∈ connectedComponentIn (Omega p) zs)
    (g : ℂ → ℝ) (hg : Continuous g)
    (hbar : ∀ z, g z = 0 → 1 ≤ ‖p.eval z‖) (hneg : g zs < 0) :
    ¬ 0 < g w := by
  intro hpos
  have hpre : IsPreconnected (connectedComponentIn (Omega p) zs) :=
    isPreconnected_connectedComponentIn
  have hzero : (0 : ℝ) ∈ g '' connectedComponentIn (Omega p) zs :=
    hpre.intermediate_value (mem_connectedComponentIn hzs) hw
      hg.continuousOn ⟨hneg.le, hpos.le⟩
  obtain ⟨v, hv, hgv⟩ := hzero
  have hvlt : ‖p.eval v‖ < 1 := connectedComponentIn_subset (Omega p) zs hv
  exact (not_lt_of_ge (hbar v hgv)) hvlt
