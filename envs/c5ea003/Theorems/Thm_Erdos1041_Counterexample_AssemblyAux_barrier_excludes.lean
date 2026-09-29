-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_barrier_excludes
-- name    : Erdos1041.Counterexample.AssemblyAux.barrier_excludes
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:18:16.313063+00:00
-- url     : https://prove2.me/theorems/c895a67d-f507-459c-8419-6cc574c2195c
-- title:
--   A signed barrier excludes a point from the component
-- statement:
--   If a continuous real function g is negative at zs inside |p|<1 and every zero of g lies where |p|≥1, then no point w in zs’s connected lemniscate component has g(w)>0.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Assembly.lean#L90-L105
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

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

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.AssemblyAux
noncomputable section
open scoped ComplexConjugate ENNReal

open Erdos1041.Counterexample.AssemblyAux

theorem Erdos1041.Counterexample.AssemblyAux.barrier_excludes (p : Polynomial ℂ) (zs w : ℂ)
    (hzs : zs ∈ Omega p) (hw : w ∈ connectedComponentIn (Omega p) zs)
    (g : ℂ → ℝ) (hg : Continuous g)
    (hbar : ∀ z, g z = 0 → 1 ≤ ‖p.eval z‖) (hneg : g zs < 0) :
    ¬ 0 < g w := by sorry
