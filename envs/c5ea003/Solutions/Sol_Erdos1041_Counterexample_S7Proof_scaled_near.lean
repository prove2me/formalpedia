-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.scaled_near
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:00.675999+00:00
-- url     : https://prove2.me/submissions/e1c6a371-4bb4-4566-9c28-8f91a188ce87

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_norm_div_sub
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_scale_cast
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_scale_pos
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
theorem solution (zs : ℂ)
    (hnear : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    ‖zs / (scaleR : ℂ) - centre‖ < 1 / 1000 := by
  have hcentre : (scaleR : ℂ) * centre =
      (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I := by
    rw [scale_cast]
    unfold centre
    norm_num
    <;> ring
  rw [norm_div_sub zs centre scaleR scale_pos, hcentre]
  apply (div_lt_iff₀ scale_pos).2
  simpa [scaleR, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hnear
