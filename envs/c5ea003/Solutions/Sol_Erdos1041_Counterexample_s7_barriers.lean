-- Prove2me | solution 1 for Erdos1041.Counterexample.s7_barriers
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:34:45.63459+00:00
-- url     : https://prove2.me/submissions/3ecd79bb-490c-4213-baad-08b5414d7c03

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_G1_negative_near
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_G1_positive_disk
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_G1_zero_norm
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_G2_negative_near
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_G2_positive_disk
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_G2_zero_norm
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_centre1_margin
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_centre2_margin
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_continuous_g1__c55f85
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_continuous_g2__ce1d1a
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_rootScale_ge
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_scaled_near
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_scaled_root_disk
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_unscale
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

section
noncomputable section
namespace Erdos1041.Counterexample.S7Proof
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
theorem s7_barriers' (zs : ℂ)
    (hnear : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    ∃ g₁ g₂ : ℂ → ℝ, Continuous g₁ ∧ Continuous g₂ ∧
      (∀ z, g₁ z = 0 → 1 ≤ ‖f.eval z‖) ∧ (∀ z, g₂ z = 0 → 1 ≤ ‖f.eval z‖) ∧
      g₁ zs < 0 ∧ g₂ zs < 0 ∧
      (∀ j : Fin 7, j.val = 0 ∨ j.val = 1 ∨ j.val = 2 →
        ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₁ w) ∧
      (∀ j : Fin 7, j.val = 4 ∨ j.val = 5 →
        ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₂ w) := by
  refine ⟨g1, g2, continuous_g1, continuous_g2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h := G1_zero_norm (z / (scaleR : ℂ)) hz
    simpa only [unscale] using h
  · intro z hz
    have h := G2_zero_norm (z / (scaleR : ℂ)) hz
    simpa only [unscale] using h
  · exact G1_negative_near (zs / (scaleR : ℂ)) (scaled_near zs hnear)
  · exact G2_negative_near (zs / (scaleR : ℂ)) (scaled_near zs hnear)
  · intro j hj w hw
    exact G1_positive_disk rootScale rootScale_ge (u j.val) (w / (scaleR : ℂ))
      (centre1_margin j.val hj) (scaled_root_disk j.val w hw)
  · intro j hj w hw
    exact G2_positive_disk rootScale rootScale_ge (u j.val) (w / (scaleR : ℂ))
      (centre2_margin j.val hj) (scaled_root_disk j.val w hw)
end Erdos1041.Counterexample.S7Proof
end
end

noncomputable section

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (zs : ℂ)
    (hnear : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    ∃ g₁ g₂ : ℂ → ℝ, Continuous g₁ ∧ Continuous g₂ ∧
      (∀ z, g₁ z = 0 → 1 ≤ ‖f.eval z‖) ∧ (∀ z, g₂ z = 0 → 1 ≤ ‖f.eval z‖) ∧
      g₁ zs < 0 ∧ g₂ zs < 0 ∧
      (∀ j : Fin 7, j.val = 0 ∨ j.val = 1 ∨ j.val = 2 →
        ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₁ w) ∧
      (∀ j : Fin 7, j.val = 4 ∨ j.val = 5 →
        ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₂ w) :=
  S7Proof.s7_barriers' zs hnear
