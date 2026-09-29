-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.K0_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:08:32.312815+00:00
-- url     : https://prove2.me/submissions/fa13f08b-da44-46f7-96d8-892e6cb52371

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pow7_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
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

noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
theorem rho_pow14_ge : (9 : ℝ) / 10 ≤ (ρ : ℝ) ^ 14 := by
  have hb : (1 : ℝ) + 14 * (-(1 / 10 ^ 96)) ≤ (1 + -(1 / 10 ^ 96)) ^ 14 := by
    apply one_add_mul_le_pow
    norm_num
  have he : (1 : ℝ) + -(1 / 10 ^ 96) = (ρ : ℝ) := by
    unfold ρ s; push_cast; ring
  rw [he] at hb
  nlinarith [hb]
theorem K0_denom_pos : (0 : ℝ) < 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 := by
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 14 := pow_pos rho_pos 14
  nlinarith [h1, eps_pow7_pos]
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : K0 ≤ 1 / 10 ^ 11 := by
  unfold K0
  have h1 : (1 : ℝ) - (ρ : ℝ) ^ 14 ≤ 14 / 10 ^ 96 := by
    have hb : (1 : ℝ) + 14 * (-(1 / 10 ^ 96)) ≤ (1 + -(1 / 10 ^ 96)) ^ 14 := by
      apply one_add_mul_le_pow; norm_num
    have he : (1 : ℝ) + -(1 / 10 ^ 96) = (ρ : ℝ) := by unfold ρ s; push_cast; ring
    rw [he] at hb
    linarith
  have h2 : (9 : ℝ) / 10 ≤ (ρ : ℝ) ^ 14 := rho_pow14_ge
  have he7 : ((ε : ℝ)) ^ 7 = 1 / 10 ^ 84 := by unfold ε s; push_cast; norm_num
  rw [div_le_iff₀ K0_denom_pos, he7]
  nlinarith [h1, h2]
