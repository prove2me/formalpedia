-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_var_on_disk
-- name    : Erdos1041.Counterexample.S4Proofs.Q_var_on_disk
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:08:39.400433+00:00
-- url     : https://prove2.me/theorems/8f514ac0-839a-4e1b-87ca-dc34ce15fd1f
-- title:
--   Taylor coefficient bounds control Q on a disk
-- statement:
--   For disk radius rr≥0 and upper bounds gj on the norms of qTj(v), the variation |Q(w)−qT0(v)| on |w−v|≤rr is at most Σ(j=1..7) gj rrʲ.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L1298-L1346
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

open Erdos1041.Counterexample.S4Proofs

theorem Erdos1041.Counterexample.S4Proofs.Q_var_on_disk {v : ℂ} {rr g1 g2 g3 g4 g5 g6 g7 : ℝ} (hr : 0 ≤ rr)
    (h1 : ‖qT1 v‖ ≤ g1) (h2 : ‖qT2 v‖ ≤ g2) (h3 : ‖qT3 v‖ ≤ g3) (h4 : ‖qT4 v‖ ≤ g4)
    (h5 : ‖qT5 v‖ ≤ g5) (h6 : ‖qT6 v‖ ≤ g6) (h7 : ‖qT7‖ ≤ g7) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr →
      ‖Q.eval w - qT0 v‖
        ≤ g1 * rr + g2 * rr ^ 2 + g3 * rr ^ 3 + g4 * rr ^ 4 + g5 * rr ^ 5 + g6 * rr ^ 6
          + g7 * rr ^ 7 := by sorry
