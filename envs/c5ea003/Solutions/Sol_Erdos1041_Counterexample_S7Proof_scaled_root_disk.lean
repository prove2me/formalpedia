-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.scaled_root_disk
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:36.118972+00:00
-- url     : https://prove2.me/submissions/20541fad-46e4-4f0e-ba46-489126d42a4d

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_norm_div_sub
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_scale_pos
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_scale_rootScale
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

noncomputable section

namespace Erdos1041.Counterexample.S7Proof
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
end Erdos1041.Counterexample.S7Proof

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S7Proof
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (j : ℕ) (w : ℂ)
    (hw : ‖w - (ρ : ℂ) * u j‖ < (ρ : ℝ) / 10) :
    ‖w / (scaleR : ℂ) - (rootScale : ℂ) * u j‖ < rootScale / 10 := by
  have hm : (scaleR : ℂ) * (rootScale : ℂ) = (ρ : ℂ) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) scale_rootScale
    simpa using h
  rw [norm_div_sub w ((rootScale : ℂ) * u j) scaleR scale_pos]
  rw [← mul_assoc, hm]
  apply (div_lt_iff₀ scale_pos).2
  have hscale : rootScale / 10 * scaleR = (ρ : ℝ) / 10 := by
    calc
      rootScale / 10 * scaleR = (scaleR * rootScale) / 10 := by ring
      _ = (ρ : ℝ) / 10 := by rw [scale_rootScale]
  simpa only [hscale] using hw
