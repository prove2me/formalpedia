-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.s4_disk_package
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:28:18.198649+00:00
-- url     : https://prove2.me/submissions/9ec98fdf-0701-4511-b35d-9aabec62d70e

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_delta_le
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_qT2_zc2_lower
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_disk_bound
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
noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
theorem aHat_norm : ‖aHat‖ = ‖qT2 zc2‖ * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 := by
  unfold aHat
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ratCast, Complex.norm_ratCast,
    abs_of_pos rho_pos, abs_of_pos eps_pos]
theorem aHat_lower : 180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ := by
  rw [aHat_norm]
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 5 := pow_pos rho_pos 5
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 5 := pow_pos eps_pos 5
  nlinarith [qT2_zc2_lower, h1, h2, mul_pos h1 h2]
theorem aHat_ne_zero : aHat ≠ 0 := by
  intro h
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 5 := pow_pos rho_pos 5
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 5 := pow_pos eps_pos 5
  have := aHat_lower
  rw [h, norm_zero] at this
  nlinarith [this, mul_pos h1 h2]
theorem slit_lt : 1 - ‖f.eval zs‖ < ‖aHat‖ * ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 / 4 := by
  have hd := delta_le
  have hp7 : (0 : ℝ) < (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 :=
    mul_pos (pow_pos rho_pos 7) (pow_pos eps_pos 7)
  have ha : 180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ := aHat_lower
  have hkey : (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6)
      < (180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5) * ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 / 4 := by
    nlinarith [hp7]
  have hmono : (180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5) * ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 / 4
      ≤ ‖aHat‖ * ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 / 4 := by
    have hsq : (0 : ℝ) ≤ ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 := sq_nonneg _
    nlinarith [ha, hsq]
  linarith [hd, hkey, hmono]
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution :
    ∃ (aHat : ℂ) (hh : ℝ), aHat ≠ 0 ∧ 0 < hh ∧
      180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ ∧
      (∀ z : ℂ, ‖z‖ ≤ hh → ‖(shiftQuad f zs).eval z / aHat - 1‖ ≤ 1 / 4) ∧
      1 - ‖f.eval zs‖ < ‖aHat‖ * hh ^ 2 / 4 :=
  ⟨aHat, (ρ : ℝ) * (ε : ℝ) / 10, aHat_ne_zero,
    by have := rho_pos; have := eps_pos; positivity, aHat_lower, disk_bound, slit_lt⟩
