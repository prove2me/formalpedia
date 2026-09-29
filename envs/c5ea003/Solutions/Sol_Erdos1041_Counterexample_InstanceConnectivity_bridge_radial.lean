-- Prove2me | solution 1 for Erdos1041.Counterexample.InstanceConnectivity.bridge_radial
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:07:40.279247+00:00
-- url     : https://prove2.me/submissions/da383d4e-a0a6-4e15-9aca-01336023d767

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Theorems.Thm_Erdos1041_Counterexample_InstanceConnectivity_root_norm_le
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open scoped ComplexConjugate

namespace Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem rho_pos : 0 < (ρ : ℝ) := by
  norm_num [ρ, s]
theorem epsilon_pos : 0 < (ε : ℝ) := by
  norm_num [ε, s]
theorem f_eval_scale (z : ℂ) :
    f.eval ((ρ : ℂ) * z) = (ρ : ℂ) ^ 7 * F.eval z := by
  simp only [f, F, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring
theorem F_eval (z : ℂ) :
    F.eval z = z ^ 7 - 1
      + (ε : ℂ) ^ 6 * p1 * z + (ε : ℂ) ^ 5 * p2 * z ^ 2 + (ε : ℂ) ^ 4 * p3 * z ^ 3
      + (ε : ℂ) ^ 3 * p4 * z ^ 4 + (ε : ℂ) ^ 2 * p5 * z ^ 5 + (ε : ℂ) * p6 * z ^ 6 := by
  simp only [F, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num [a, b, c, A, B, Cconst, t, s, ε, p1, p2, p3, p4, p5, p6, Complex.conj_ofNat]
  ring
theorem norm_le_of_normSq_le {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : Complex.normSq z ≤ r ^ 2) :
    ‖z‖ ≤ r := by
  nlinarith [Complex.sq_norm z, norm_nonneg z]
theorem norm_p1 : ‖p1‖ ≤ 720 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p1, Complex.normSq_apply])
theorem norm_p2 : ‖p2‖ ≤ 690 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p2, Complex.normSq_apply])
theorem norm_p3 : ‖p3‖ ≤ 206 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p3, Complex.normSq_apply])
theorem norm_p4 : ‖p4‖ ≤ 1 / 10 ^ 9 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p4, Complex.normSq_apply])
theorem norm_p5 : ‖p5‖ ≤ 1 / 10 ^ 30 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p5, Complex.normSq_apply])
theorem norm_p6 : ‖p6‖ ≤ 1 / 10 ^ 55 :=
  norm_le_of_normSq_le (by norm_num) (by norm_num [p6, Complex.normSq_apply])
theorem rho_lt_one : (ρ : ℝ) < 1 := by norm_num [ρ, s]
theorem rho_ne_zeroC : ((ρ : ℚ) : ℂ) ≠ 0 := by
  have h : (ρ : ℚ) ≠ 0 := by norm_num [ρ, s]
  exact_mod_cast h
theorem eps_normC : ‖((ε : ℚ) : ℂ)‖ = (ε : ℝ) := by
  rw [Complex.norm_ratCast, abs_of_pos epsilon_pos]
theorem F_root_eq (z : ℂ) (hz : F.eval z = 0) :
    z ^ 7 = 1 - ((ε:ℂ) ^ 6 * p1 * z + (ε:ℂ) ^ 5 * p2 * z ^ 2 + (ε:ℂ) ^ 4 * p3 * z ^ 3
      + (ε:ℂ) ^ 3 * p4 * z ^ 4 + (ε:ℂ) ^ 2 * p5 * z ^ 5 + (ε:ℂ) * p6 * z ^ 6) := by
  have h := F_eval z
  rw [hz] at h
  linear_combination -h
theorem joinedIn_affine_of_mem (z₀ z₁ : ℂ)
    (h : ∀ τ ∈ Set.Icc (0:ℝ) 1, z₀ + (τ : ℂ) * (z₁ - z₀) ∈ Omega f) :
    JoinedIn (Omega f) z₀ z₁ := by
  apply JoinedIn.ofLine (f := fun τ : ℝ => z₀ + (τ : ℂ) * (z₁ - z₀))
  · exact (show Continuous (fun τ : ℝ => z₀ + (τ : ℂ) * (z₁ - z₀)) from by fun_prop).continuousOn
  · norm_num
  · push_cast; ring
  · rintro _ ⟨τ, hτ, rfl⟩
    exact h τ hτ
theorem F_eval_of_root {bj : ℂ} (hroot : f.IsRoot bj) : F.eval (bj / (ρ : ℂ)) = 0 := by
  have hρ0 : ((ρ:ℚ):ℂ) ≠ 0 := rho_ne_zeroC
  have h := f_eval_scale (bj / (ρ : ℂ))
  have hb : (ρ:ℂ) * (bj / (ρ:ℂ)) = bj := by field_simp
  rw [hb, show f.eval bj = 0 from hroot] at h
  rcases mul_eq_zero.mp h.symm with h3 | h3
  · exact absurd h3 (pow_ne_zero 7 hρ0)
  · exact h3
theorem zeta_norm_le {bj : ℂ} (hroot : f.IsRoot bj) : ‖bj / (ρ : ℂ)‖ ≤ 101 / 100 :=
  root_norm_le _ (F_eval_of_root hroot)
end Erdos1041.Counterexample.InstanceConnectivity

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.InstanceConnectivity
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.InstanceConnectivity in
theorem solution (bj : ℂ) (hroot : f.IsRoot bj) :
    JoinedIn (Omega f) (8 * (ε : ℂ) * bj) bj := by
  have hρ0 : ((ρ:ℚ):ℂ) ≠ 0 := rho_ne_zeroC
  have hrp : (0:ℝ) < (ρ:ℝ) := rho_pos
  have hep : (0:ℝ) < (ε:ℝ) := epsilon_pos
  have heps : (ε:ℝ) = 1 / 10 ^ 12 := by norm_num [ε, s]
  have hFz : F.eval (bj / (ρ:ℂ)) = 0 := F_eval_of_root hroot
  have hzn : ‖bj / (ρ:ℂ)‖ ≤ 101 / 100 := zeta_norm_le hroot
  have hz7 := F_root_eq _ hFz
  apply joinedIn_affine_of_mem
  intro τ hτ
  set v : ℝ := 8 * (ε:ℝ) + τ * (1 - 8 * (ε:ℝ)) with hvdef
  have hvlo : 8 * (ε:ℝ) ≤ v := by rw [heps] at *; nlinarith [hτ.1, hτ.2]
  have hvhi : v ≤ 1 := by rw [heps] at *; nlinarith [hτ.1, hτ.2]
  have hv0 : (0:ℝ) < v := by rw [heps] at *; nlinarith [hτ.1, hτ.2]
  have hpt : 8 * (ε:ℂ) * bj + (τ:ℂ) * (bj - 8 * (ε:ℂ) * bj) = ((v : ℝ) : ℂ) * bj := by
    rw [hvdef]; push_cast; ring
  rw [hpt]
  -- transport to the model polynomial
  have hfv : f.eval (((v:ℝ):ℂ) * bj) = (ρ:ℂ) ^ 7 * F.eval (((v:ℝ):ℂ) * (bj / (ρ:ℂ))) := by
    rw [← f_eval_scale]; congr 1; field_simp
  have hid : F.eval (((v:ℝ):ℂ) * (bj / (ρ:ℂ))) = (((v:ℝ):ℂ) ^ 7 - 1)
      + ((ε:ℂ) ^ 6 * p1 * (bj / (ρ:ℂ)) * (((v:ℝ):ℂ) - ((v:ℝ):ℂ) ^ 7)
        + (ε:ℂ) ^ 5 * p2 * (bj / (ρ:ℂ)) ^ 2 * (((v:ℝ):ℂ) ^ 2 - ((v:ℝ):ℂ) ^ 7)
        + (ε:ℂ) ^ 4 * p3 * (bj / (ρ:ℂ)) ^ 3 * (((v:ℝ):ℂ) ^ 3 - ((v:ℝ):ℂ) ^ 7)
        + (ε:ℂ) ^ 3 * p4 * (bj / (ρ:ℂ)) ^ 4 * (((v:ℝ):ℂ) ^ 4 - ((v:ℝ):ℂ) ^ 7)
        + (ε:ℂ) ^ 2 * p5 * (bj / (ρ:ℂ)) ^ 5 * (((v:ℝ):ℂ) ^ 5 - ((v:ℝ):ℂ) ^ 7)
        + (ε:ℂ) * p6 * (bj / (ρ:ℂ)) ^ 6 * (((v:ℝ):ℂ) ^ 6 - ((v:ℝ):ℂ) ^ 7)) := by
    rw [F_eval]
    linear_combination (((v:ℝ):ℂ)) ^ 7 * hz7
  have hvC : ∀ k : ℕ, k ≤ 7 → ‖((v:ℝ):ℂ) ^ k - ((v:ℝ):ℂ) ^ 7‖ ≤ v ^ k := by
    intro k hk
    have h : ((v:ℝ):ℂ) ^ k - ((v:ℝ):ℂ) ^ 7 = (((v ^ k - v ^ 7 : ℝ)) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 : v ^ 7 ≤ v ^ k := pow_le_pow_of_le_one (le_of_lt hv0) hvhi hk
    have h2 : (0:ℝ) ≤ v ^ 7 := by positivity
    constructor <;> nlinarith
  have hepsv : ∀ j k : ℕ, j + k = 7 → (ε:ℝ) ^ j * v ^ k ≤ v ^ 7 / 8 ^ j := by
    intro j k hjk
    have h80 : (0:ℝ) ≤ 8 * (ε:ℝ) := by linarith
    have h1 : (8 * (ε:ℝ)) ^ j ≤ v ^ j := pow_le_pow_left₀ h80 hvlo j
    have h2 : (8 * (ε:ℝ)) ^ j = 8 ^ j * (ε:ℝ) ^ j := mul_pow 8 _ j
    have h3 : (0:ℝ) < v ^ k := by positivity
    have h4 : v ^ 7 = v ^ j * v ^ k := by rw [← pow_add, hjk]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (8:ℝ) ^ j), h4]
    nlinarith [h1, h2, h3]
  have hT : ∀ (j k : ℕ) (pk : ℂ) (U : ℝ), ‖pk‖ ≤ U → 0 ≤ U → k ≤ 6 → j + k = 7 →
      ‖(ε:ℂ) ^ j * pk * (bj / (ρ:ℂ)) ^ k * (((v:ℝ):ℂ) ^ k - ((v:ℝ):ℂ) ^ 7)‖
        ≤ U * (107 / 100 : ℝ) * (v ^ 7 / 8 ^ j) := by
    intro j k pk U hU hU0 hk hjk
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, eps_normC]
    have c1 : ‖bj / (ρ:ℂ)‖ ^ k ≤ (107 / 100 : ℝ) := by
      calc ‖bj / (ρ:ℂ)‖ ^ k ≤ (101/100:ℝ) ^ k := pow_le_pow_left₀ (norm_nonneg _) hzn k
        _ ≤ (101/100:ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hk
        _ ≤ 107 / 100 := by norm_num
    have c2 : ‖((v:ℝ):ℂ) ^ k - ((v:ℝ):ℂ) ^ 7‖ ≤ v ^ k := hvC k (by omega)
    have c3 : (ε:ℝ) ^ j * v ^ k ≤ v ^ 7 / 8 ^ j := hepsv j k hjk
    have c4 : (0:ℝ) ≤ (ε:ℝ) ^ j := pow_nonneg (le_of_lt hep) j
    have c5 : (0:ℝ) ≤ ‖bj / (ρ:ℂ)‖ ^ k := by positivity
    have c6 : (0:ℝ) ≤ ‖((v:ℝ):ℂ) ^ k - ((v:ℝ):ℂ) ^ 7‖ := norm_nonneg _
    have c7 : (0:ℝ) ≤ v ^ k := by positivity
    have c8 : (0:ℝ) ≤ ‖pk‖ := norm_nonneg pk
    calc (ε:ℝ) ^ j * ‖pk‖ * ‖bj / (ρ:ℂ)‖ ^ k * ‖((v:ℝ):ℂ) ^ k - ((v:ℝ):ℂ) ^ 7‖
        ≤ (ε:ℝ) ^ j * U * (107/100 : ℝ) * v ^ k := by
          apply mul_le_mul (mul_le_mul (by nlinarith) c1 c5 (by nlinarith)) c2 c6 (by nlinarith)
      _ = U * (107/100 : ℝ) * ((ε:ℝ) ^ j * v ^ k) := by ring
      _ ≤ U * (107/100 : ℝ) * (v ^ 7 / 8 ^ j) := by nlinarith
  have d1 := hT 6 1 p1 720 norm_p1 (by norm_num) (by norm_num) (by norm_num)
  have d2 := hT 5 2 p2 690 norm_p2 (by norm_num) (by norm_num) (by norm_num)
  have d3 := hT 4 3 p3 206 norm_p3 (by norm_num) (by norm_num) (by norm_num)
  have d4 := hT 3 4 p4 (1/10^9) norm_p4 (by norm_num) (by norm_num) (by norm_num)
  have d5 := hT 2 5 p5 (1/10^30) norm_p5 (by norm_num) (by norm_num) (by norm_num)
  have d6 := hT 1 6 p6 (1/10^55) norm_p6 (by norm_num) (by norm_num) (by norm_num)
  have hd6 : ‖(ε:ℂ) * p6 * (bj / (ρ:ℂ)) ^ 6 * (((v:ℝ):ℂ) ^ 6 - ((v:ℝ):ℂ) ^ 7)‖
      ≤ (1/10^55 : ℝ) * (107/100) * (v ^ 7 / 8 ^ 1) := by simpa using d6
  have hd1 : ‖(ε:ℂ) ^ 6 * p1 * (bj / (ρ:ℂ)) * (((v:ℝ):ℂ) - ((v:ℝ):ℂ) ^ 7)‖
      ≤ (720:ℝ) * (107/100) * (v ^ 7 / 8 ^ 6) := by simpa using d1
  set S1 := (ε:ℂ) ^ 6 * p1 * (bj / (ρ:ℂ)) * (((v:ℝ):ℂ) - ((v:ℝ):ℂ) ^ 7) with hS1
  set S2 := (ε:ℂ) ^ 5 * p2 * (bj / (ρ:ℂ)) ^ 2 * (((v:ℝ):ℂ) ^ 2 - ((v:ℝ):ℂ) ^ 7) with hS2
  set S3 := (ε:ℂ) ^ 4 * p3 * (bj / (ρ:ℂ)) ^ 3 * (((v:ℝ):ℂ) ^ 3 - ((v:ℝ):ℂ) ^ 7) with hS3
  set S4 := (ε:ℂ) ^ 3 * p4 * (bj / (ρ:ℂ)) ^ 4 * (((v:ℝ):ℂ) ^ 4 - ((v:ℝ):ℂ) ^ 7) with hS4
  set S5 := (ε:ℂ) ^ 2 * p5 * (bj / (ρ:ℂ)) ^ 5 * (((v:ℝ):ℂ) ^ 5 - ((v:ℝ):ℂ) ^ 7) with hS5
  set S6 := (ε:ℂ) * p6 * (bj / (ρ:ℂ)) ^ 6 * (((v:ℝ):ℂ) ^ 6 - ((v:ℝ):ℂ) ^ 7) with hS6
  have t1 := norm_add_le (S1 + S2 + S3 + S4 + S5) S6
  have t2 := norm_add_le (S1 + S2 + S3 + S4) S5
  have t3 := norm_add_le (S1 + S2 + S3) S4
  have t4 := norm_add_le (S1 + S2) S3
  have t5 := norm_add_le S1 S2
  have hv7 : (0:ℝ) < v ^ 7 := by positivity
  have hnum : (720:ℝ) * (107/100) * (v ^ 7 / 8 ^ 6) + 690 * (107/100) * (v ^ 7 / 8 ^ 5)
      + 206 * (107/100) * (v ^ 7 / 8 ^ 4) + (1/10^9 : ℝ) * (107/100) * (v ^ 7 / 8 ^ 3)
      + (1/10^30 : ℝ) * (107/100) * (v ^ 7 / 8 ^ 2)
      + (1/10^55 : ℝ) * (107/100) * (v ^ 7 / 8 ^ 1) ≤ (793/10000 : ℝ) * v ^ 7 := by
    nlinarith [hv7]
  have hStail : ‖S1 + S2 + S3 + S4 + S5 + S6‖ ≤ (793/10000 : ℝ) * v ^ 7 := by linarith
  have hv7le : v ^ 7 ≤ 1 := pow_le_one₀ (le_of_lt hv0) hvhi
  have hlead : ‖((v:ℝ):ℂ) ^ 7 - 1‖ = 1 - v ^ 7 := by
    have h : ((v:ℝ):ℂ) ^ 7 - 1 = (((v ^ 7 - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hFbound : ‖F.eval (((v:ℝ):ℂ) * (bj / (ρ:ℂ)))‖ ≤ 1 - (9207/10000 : ℝ) * v ^ 7 := by
    rw [hid]
    refine le_trans (norm_add_le _ _) ?_
    rw [hlead]
    linarith
  show ‖f.eval (((v:ℝ):ℂ) * bj)‖ < 1
  rw [hfv, norm_mul, norm_pow, Complex.norm_ratCast, abs_of_pos hrp]
  have hr7 : (ρ:ℝ) ^ 7 ≤ 1 := pow_le_one₀ (le_of_lt hrp) (le_of_lt rho_lt_one)
  have hr7p : (0:ℝ) < (ρ:ℝ) ^ 7 := by positivity
  have hFn : (0:ℝ) ≤ ‖F.eval (((v:ℝ):ℂ) * (bj / (ρ:ℂ)))‖ := norm_nonneg _
  have hcle : (9207/10000 : ℝ) * v ^ 7 ≤ 9207 / 10000 := by nlinarith [hv7le]
  have step1 : (ρ:ℝ) ^ 7 * ‖F.eval (((v:ℝ):ℂ) * (bj / (ρ:ℂ)))‖
      ≤ (ρ:ℝ) ^ 7 * (1 - (9207/10000 : ℝ) * v ^ 7) :=
    mul_le_mul_of_nonneg_left hFbound (le_of_lt hr7p)
  have hprod : (0:ℝ) ≤ (1 - (ρ:ℝ) ^ 7) * (1 - (9207/10000 : ℝ) * v ^ 7) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [step1, hprod, hv7]
