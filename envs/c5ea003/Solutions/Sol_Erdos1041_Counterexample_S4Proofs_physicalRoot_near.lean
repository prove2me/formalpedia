-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.physicalRoot_near
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:40:10.686958+00:00
-- url     : https://prove2.me/submissions/39e02164-fe3d-48f3-aeaf-46a66e61da8a

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_realRoot_mem
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_norm_cayley_sub_lt
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_0
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_1
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_2
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_3
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_4
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_5
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_6
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
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
theorem cayley_near_u_0 : ‖cayley (realRoot 0) - u 0‖ < 1 / 10 := by
  have hx1 : (-1 / 10000 : ℝ) < realRoot 0 := (realRoot_mem 0).1
  have hx2 : realRoot 0 < (1 / 10000 : ℝ) := (realRoot_mem 0).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_0
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
theorem cayley_near_u_1 : ‖cayley (realRoot 1) - u 1‖ < 1 / 10 := by
  have hx1 : (4815 / 10000 : ℝ) < realRoot 1 := (realRoot_mem 1).1
  have hx2 : realRoot 1 < (4816 / 10000 : ℝ) := (realRoot_mem 1).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_1
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
theorem cayley_near_u_2 : ‖cayley (realRoot 2) - u 2‖ < 1 / 10 := by
  have hx1 : (12539 / 10000 : ℝ) < realRoot 2 := (realRoot_mem 2).1
  have hx2 : realRoot 2 < (12540 / 10000 : ℝ) := (realRoot_mem 2).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_2
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
theorem cayley_near_u_3 : ‖cayley (realRoot 3) - u 3‖ < 1 / 10 := by
  have hx1 : (43812 / 10000 : ℝ) < realRoot 3 := (realRoot_mem 3).1
  have hx2 : realRoot 3 < (43813 / 10000 : ℝ) := (realRoot_mem 3).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_3
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
theorem cayley_near_u_4 : ‖cayley (realRoot 4) - u 4‖ < 1 / 10 := by
  have hx1 : (-43813 / 10000 : ℝ) < realRoot 4 := (realRoot_mem 4).1
  have hx2 : realRoot 4 < (-43812 / 10000 : ℝ) := (realRoot_mem 4).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_4
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
theorem cayley_near_u_5 : ‖cayley (realRoot 5) - u 5‖ < 1 / 10 := by
  have hx1 : (-12540 / 10000 : ℝ) < realRoot 5 := (realRoot_mem 5).1
  have hx2 : realRoot 5 < (-12539 / 10000 : ℝ) := (realRoot_mem 5).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_5
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
theorem cayley_near_u_6 : ‖cayley (realRoot 6) - u 6‖ < 1 / 10 := by
  have hx1 : (-4816 / 10000 : ℝ) < realRoot 6 := (realRoot_mem 6).1
  have hx2 : realRoot 6 < (-4815 / 10000 : ℝ) := (realRoot_mem 6).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_6
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
theorem cayley_near_u (j : Fin 7) : ‖cayley (realRoot j) - u (j : ℕ)‖ < 1 / 10 := by
  fin_cases j
  · exact cayley_near_u_0
  · exact cayley_near_u_1
  · exact cayley_near_u_2
  · exact cayley_near_u_3
  · exact cayley_near_u_4
  · exact cayley_near_u_5
  · exact cayley_near_u_6
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution (j : Fin 7) :
    ‖physicalRoot j - (ρ : ℂ) * u (j : ℕ)‖ < (ρ : ℝ) / 10 := by
  have h : physicalRoot j - (ρ : ℂ) * u (j : ℕ)
      = (ρ : ℂ) * (cayley (realRoot j) - u (j : ℕ)) := by
    unfold physicalRoot; ring
  rw [h, norm_mul, Complex.norm_ratCast, abs_of_pos rho_pos]
  nlinarith [rho_pos, cayley_near_u j, norm_nonneg (cayley (realRoot j) - u (j : ℕ))]
