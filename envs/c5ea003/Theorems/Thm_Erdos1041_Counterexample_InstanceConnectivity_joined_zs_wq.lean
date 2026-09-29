-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_joined_zs_wq
-- name    : Erdos1041.Counterexample.InstanceConnectivity.joined_zs_wq
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:07:01.895235+00:00
-- url     : https://prove2.me/theorems/60a56baf-2df9-4867-980a-f5c200d968b2
-- title:
--   The critical point joins the rational center
-- statement:
--   If zs is a critical point in the stated ρε/1000 neighborhood of the explicit center, it joins scale(wq) inside |f|<1.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceConnectivity.lean#L1287-L1310
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
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

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
noncomputable section
open scoped ComplexConjugate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Erdos1041.Counterexample.InstanceConnectivity

theorem Erdos1041.Counterexample.InstanceConnectivity.joined_zs_wq (zs : ℂ)
    (hcrit : (Polynomial.derivative f).IsRoot zs)
    (hloc : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ)) : ℂ) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    JoinedIn (Omega f) zs (scale wq) := by sorry
