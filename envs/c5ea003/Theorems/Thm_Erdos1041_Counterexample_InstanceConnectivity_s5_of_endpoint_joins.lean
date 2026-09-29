-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_s5_of_endpoint_joins
-- name    : Erdos1041.Counterexample.InstanceConnectivity.s5_of_endpoint_joins
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:07:03.253729+00:00
-- url     : https://prove2.me/theorems/5b4cacad-5571-4605-b443-6205e308b4a8
-- title:
--   Three certified joins place both roots in one component
-- statement:
--   If zs joins scale(wq) and scale(m3), scale(m6) respectively join b₃,b₆ inside |f|<1, then both b₃ and b₆ lie in zs’s connected component of the strict lemniscate.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceConnectivity.lean#L427-L436
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

theorem Erdos1041.Counterexample.InstanceConnectivity.s5_of_endpoint_joins (zs b₃ b₆ : ℂ)
    (hstart : JoinedIn (Omega f) zs (scale wq))
    (hend₃ : JoinedIn (Omega f) (scale m3) b₃)
    (hend₆ : JoinedIn (Omega f) (scale m6) b₆) :
    b₃ ∈ connectedComponentIn (Omega f) zs ∧
      b₆ ∈ connectedComponentIn (Omega f) zs := by sorry
