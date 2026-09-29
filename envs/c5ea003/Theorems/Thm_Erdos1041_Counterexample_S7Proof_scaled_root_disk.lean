-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S7Proof_scaled_root_disk
-- name    : Erdos1041.Counterexample.S7Proof.scaled_root_disk
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:24:11.911197+00:00
-- url     : https://prove2.me/theorems/eba04778-651e-4306-a84a-69cca12e954b
-- title:
--   Physical root disks become model root disks
-- statement:
--   If w is within ρ/10 of the scaled root-of-unity point ρu(j), then w/scaleR is within rootScale/10 of rootScale·u(j).
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceBarriers.lean#L45-L58
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
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

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S7Proof
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

open Erdos1041.Counterexample.S7Proof

theorem Erdos1041.Counterexample.S7Proof.scaled_root_disk (j : ℕ) (w : ℂ)
    (hw : ‖w - (ρ : ℂ) * u j‖ < (ρ : ℝ) / 10) :
    ‖w / (scaleR : ℂ) - (rootScale : ℂ) * u j‖ < rootScale / 10 := by sorry
