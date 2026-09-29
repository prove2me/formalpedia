-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S4Proofs_one_sub_sq_norm_f_rho_eps
-- name    : Erdos1041.Counterexample.S4Proofs.one_sub_sq_norm_f_rho_eps
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:19:26.045+00:00
-- url     : https://prove2.me/theorems/544e8032-afc7-4760-80d1-4f71da7aa3b2
-- title:
--   The squared-norm margin is a positive scale of Hs
-- statement:
--   For every complex w, 1−|f(ρεw)|²=2ρ¹⁴ε⁷ Hs(w).
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L889-L894
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
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Erdos1041.Counterexample.S4Proofs

theorem Erdos1041.Counterexample.S4Proofs.one_sub_sq_norm_f_rho_eps (w : ℂ) :
    1 - ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ ^ 2
      = 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs w := by sorry
