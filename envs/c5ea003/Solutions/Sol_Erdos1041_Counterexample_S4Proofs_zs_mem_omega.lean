-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.zs_mem_omega
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:22:03.763803+00:00
-- url     : https://prove2.me/submissions/c5edb0a5-a9eb-4b8b-b4c4-37b70fdd539c

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Hs_pos_vc2
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_one_sub_sq_norm_f_rho_eps
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
theorem mem_omega_of_Hs_pos {w : ℂ} (h : 0 < Hs w) :
    ((ρ : ℂ) * (ε : ℂ) * w) ∈ Omega f := by
  have hid := one_sub_sq_norm_f_rho_eps w
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 14 := pow_pos rho_pos 14
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 7 := pow_pos eps_pos 7
  have hpos : 0 < 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs w := by positivity
  have hlt : ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ ^ 2 < 1 := by linarith [hid, hpos]
  have hn := norm_nonneg (f.eval ((ρ : ℂ) * (ε : ℂ) * w))
  show ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ < 1
  nlinarith [hlt, hn]
theorem Hs_zc2_pos : 0 < Hs zc2 := Hs_pos_vc2 zc2 zc2_mem
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
set_option maxHeartbeats 4000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution : zs ∈ Omega f := mem_omega_of_Hs_pos Hs_zc2_pos
