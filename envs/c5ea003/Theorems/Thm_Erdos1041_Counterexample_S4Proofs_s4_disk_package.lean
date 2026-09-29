-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S4Proofs_s4_disk_package
-- name    : Erdos1041.Counterexample.S4Proofs.s4_disk_package
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:28:02.674602+00:00
-- url     : https://prove2.me/theorems/07a62248-ad0b-4e45-a2cf-84df1bfc35e4
-- title:
--   A quadratic disk certificate at the interior critical point
-- statement:
--   There are a nonzero complex coefficient â and radius h>0 with |â|≥180ρ⁵ε⁵; on |z|≤h the normalized shifted quadratic polynomial differs from 1 by at most 1/4, and the depth 1−|f(zs)| is smaller than |â|h²/4.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L4069-L4075
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

theorem Erdos1041.Counterexample.S4Proofs.s4_disk_package :
    ∃ (aHat : ℂ) (hh : ℝ), aHat ≠ 0 ∧ 0 < hh ∧
      180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ ∧
      (∀ z : ℂ, ‖z‖ ≤ hh → ‖(shiftQuad f zs).eval z / aHat - 1‖ ≤ 1 / 4) ∧
      1 - ‖f.eval zs‖ < ‖aHat‖ * hh ^ 2 / 4 := by sorry
