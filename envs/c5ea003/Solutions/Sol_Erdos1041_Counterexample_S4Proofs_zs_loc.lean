-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.zs_loc
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:28:31.393519+00:00
-- url     : https://prove2.me/submissions/342a0b3b-54a7-48c0-9a03-8e513035bf98

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pos
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
noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
theorem zc2_mem : ‖zc2 - vc2‖ ≤ 1 / 1000000 := by
  have h := crit_loc_2.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
    < (ρ : ℝ) * (ε : ℝ) / 1000 := by
  have hrw : zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I
      = (ρ : ℂ) * (ε : ℂ) * (zc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I) := by
    unfold zs; ring
  have h2 : ‖vc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖ ≤ 5 / 10 ^ 7 := by
    apply norm_le_of_normSq_le (by norm_num)
    unfold vc2
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im]
    push_cast
    norm_num
  have hc : ‖zc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖ < 1 / 1000 := by
    have he : zc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I
        = (zc2 - vc2) + (vc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I) := by ring
    rw [he]
    calc ‖(zc2 - vc2) + (vc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I)‖
        ≤ ‖zc2 - vc2‖ + ‖vc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖ :=
          norm_add_le _ _
      _ < 1 / 1000 := by linarith [zc2_mem, h2]
  rw [hrw, norm_mul, norm_mul, Complex.norm_ratCast, Complex.norm_ratCast,
    abs_of_pos rho_pos, abs_of_pos eps_pos]
  have hp : (0 : ℝ) < (ρ : ℝ) * (ε : ℝ) := mul_pos rho_pos eps_pos
  have hkey := mul_lt_mul_of_pos_left hc hp
  linarith [hkey]
