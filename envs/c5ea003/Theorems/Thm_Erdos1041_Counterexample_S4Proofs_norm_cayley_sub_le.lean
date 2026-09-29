-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S4Proofs_norm_cayley_sub_le
-- name    : Erdos1041.Counterexample.S4Proofs.norm_cayley_sub_le
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:24:01.740102+00:00
-- url     : https://prove2.me/theorems/14da2646-4b42-4c98-8b38-b31d65c1da7f
-- title:
--   Rational coordinate errors bound Cayley distance
-- statement:
--   Under the stated two numerator bounds, positive denominator bound D≤1+x², and 2M²≤T²D, the distance |cayley(x)−w| is at most T.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L4084-L4121
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

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

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
noncomputable section
open scoped ComplexConjugate NNReal
noncomputable section
open scoped ComplexConjugate NNReal
set_option maxHeartbeats 4000000

open Erdos1041.Counterexample.S4Proofs

theorem Erdos1041.Counterexample.S4Proofs.norm_cayley_sub_le {x : ℝ} {w : ℂ} {M D T : ℝ} (hT : 0 ≤ T)
    (hA : |1 - w.re - w.im * x| ≤ M) (hB : |x + w.re * x - w.im| ≤ M)
    (hD : 0 < D) (hx : D ≤ 1 + x ^ 2) (hfin : 2 * M ^ 2 ≤ T ^ 2 * D) :
    ‖cayley x - w‖ ≤ T := by sorry
