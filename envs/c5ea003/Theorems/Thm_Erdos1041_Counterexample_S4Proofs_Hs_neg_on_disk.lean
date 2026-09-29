-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Hs_neg_on_disk
-- name    : Erdos1041.Counterexample.S4Proofs.Hs_neg_on_disk
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:07:49.458166+00:00
-- url     : https://prove2.me/theorems/0a841a03-a77d-423c-88b6-37dc052dfd22
-- title:
--   A center margin makes Hs negative on a disk
-- statement:
--   If Q varies by at most var on a closed disk about v, Re(qT0(v))≤reHi, and reHi+var+10⁻¹¹<0, then Hs is negative everywhere on that disk.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L1385-L1402
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

theorem Erdos1041.Counterexample.S4Proofs.Hs_neg_on_disk {v : ℂ} {rr var reHi : ℝ}
    (hvar : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w - qT0 v‖ ≤ var)
    (hre : (qT0 v).re ≤ reHi)
    (hneg : reHi + var + 1 / 10 ^ 11 < 0) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr → Hs w < 0 := by sorry
