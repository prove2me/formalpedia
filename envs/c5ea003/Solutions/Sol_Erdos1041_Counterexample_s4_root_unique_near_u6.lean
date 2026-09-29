-- Prove2me | solution 1 for Erdos1041.Counterexample.s4_root_unique_near_u6
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:33:49.004287+00:00
-- url     : https://prove2.me/submissions/f03366c1-0cd0-49f0-b0b7-ab9e5e1ec92e

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_exists_index_of_isRoot
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_0
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_1
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_2
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_3
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_4
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_5
import Theorems.Thm_Erdos1041_Counterexample_u_bounds_6
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_physicalRoot_near
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

namespace Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
theorem exp_neg_two_pi_div_seven : Complex.exp (-2 * Real.pi * Complex.I / 7) = u 6 := by
  unfold u
  have e : (2 * (Real.pi : ℂ) * ((6 : ℕ) : ℂ) * Complex.I / 7)
      = -2 * (Real.pi : ℂ) * Complex.I / 7 + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
theorem norm_sub_ge_of_box {z w : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : d ^ 2 ≤ (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) : d ≤ ‖z - w‖ := by
  have hn : ‖z - w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  nlinarith [hn, h, norm_nonneg (z - w), hd]
theorem u_sep_six (k : ℕ) (hk : k < 7) (hne : k ≠ 6) : (1 / 5 : ℝ) ≤ ‖u k - u 6‖ := by
  obtain ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ := u_bounds_6
  interval_cases k
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_0; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_1; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_2; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_3; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_4; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_5; nlinarith)
  · exact absurd rfl hne
private theorem unique_near_aux (j : Fin 7) (k : ℕ)
    (hsep : (1 / 5 : ℝ) ≤ ‖u (j : ℕ) - u k‖)
    (hnear : ‖S4Proofs.physicalRoot j - (ρ : ℂ) * u k‖ < (ρ : ℝ) / 10) : False := by
  have h1 := S4Proofs.physicalRoot_near j
  have e : (ρ : ℂ) * (u (j : ℕ) - u k)
      = (S4Proofs.physicalRoot j - (ρ : ℂ) * u k)
        - (S4Proofs.physicalRoot j - (ρ : ℂ) * u (j : ℕ)) := by ring
  have hlt : ‖(ρ : ℂ) * (u (j : ℕ) - u k)‖ < (ρ : ℝ) / 5 := by
    rw [e]
    have htri := norm_sub_le (S4Proofs.physicalRoot j - (ρ : ℂ) * u k)
      (S4Proofs.physicalRoot j - (ρ : ℂ) * u (j : ℕ))
    linarith
  rw [norm_mul, Complex.norm_ratCast, abs_of_pos S4Proofs.rho_pos] at hlt
  nlinarith [S4Proofs.rho_pos, hsep, hlt]
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution :
    ∀ w, f.IsRoot w →
      ‖w - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
      w = S4Proofs.physicalRoot 6 := by
  intro w hw hnear
  rw [exp_neg_two_pi_div_seven] at hnear
  obtain ⟨j, rfl⟩ := S4Proofs.exists_index_of_isRoot hw
  have hj : (j : ℕ) = 6 := by
    by_contra hne
    exact unique_near_aux j 6 (u_sep_six (j : ℕ) j.isLt hne) hnear
  have hje : j = 6 := by
    apply Fin.ext
    simpa using hj
  rw [hje]
