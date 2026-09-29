-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S7Proof_cert_tail_D
-- name    : Erdos1041.Counterexample.S7Proof.cert_tail_D
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:41:31.861739+00:00
-- url     : https://prove2.me/theorems/108fcbdd-fec8-4230-b3b4-a44d7c345357
-- title:
--   Nonpositive barrier tail D
-- statement:
--   For every r≥0, Hpoly is nonpositive on the affine ray from (10,-45) through (12,-54) at parameter r; this is a certificate for the second separating graph.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/BarrierCertificates.lean#L230-L244
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/


noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

open Erdos1041.Counterexample.S7Proof

theorem Erdos1041.Counterexample.S7Proof.cert_tail_D (r : ℝ) (hr0 : 0 ≤ r) :
    Hpoly (10 + (12 - 10) * r) ((-45) + ((-54) - (-45)) * r) ≤ 0 := by sorry
