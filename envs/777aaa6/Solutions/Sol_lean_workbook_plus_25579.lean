-- Prove2me | solution 1 for lean_workbook_plus_25579
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:31:50.904198+00:00
-- url     : https://prove2.me/submissions/2b1755e0-11ef-4617-a90b-f542d3cdf3b6

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

open Filter
open scoped Topology

theorem positive_values_unique (p : ℝ) (hp : 1 < p) (f : ℝ → ℝ)
    (hf : Continuous f) (heq : ∀ x : ℝ, 0 < x → f x + p * f (p * x) = 1)
    (x : ℝ) (hx : 0 < x) : f x = 1 / (p + 1) := by
  have hp0 : 0 < p := by linarith
  have hp1 : p + 1 ≠ 0 := by linarith
  have hq0 : 0 < p⁻¹ := inv_pos.mpr hp0
  let c : ℝ := 1 / (p + 1)
  have hc : (p + 1) * c = 1 := by
    dsimp [c]
    field_simp
  have hstep (t : ℝ) (ht : 0 < t) :
      (-p⁻¹) * (f (p⁻¹ * t) - c) = f t - c := by
    have h := heq (p⁻¹ * t) (mul_pos hq0 ht)
    have he : p * (p⁻¹ * t) = t := by field_simp
    rw [he] at h
    have hd : f (p⁻¹ * t) - c = -p * (f t - c) := by
      linear_combination h - hc
    rw [hd]
    field_simp
  have hiter (n : ℕ) : (-p⁻¹)^n * (f ((p⁻¹)^n * x) - c) = f x - c := by
    induction n with
    | zero => simp
    | succ n ih =>
      have ht : 0 < (p⁻¹)^n * x := mul_pos (pow_pos hq0 n) hx
      have he : (p⁻¹)^(n + 1) * x = p⁻¹ * ((p⁻¹)^n * x) := by rw [pow_succ]; ring
      calc
        (-p⁻¹)^(n + 1) * (f ((p⁻¹)^(n + 1) * x) - c) =
            (-p⁻¹)^n * ((-p⁻¹) * (f (p⁻¹ * ((p⁻¹)^n * x)) - c)) := by
              rw [he, pow_succ]
              ring
        _ = (-p⁻¹)^n * (f ((p⁻¹)^n * x) - c) := by rw [hstep _ ht]
        _ = f x - c := ih
  have hnorm : ‖p⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    exact (inv_lt_one₀ hp0).mpr hp
  have hnormNeg : ‖-p⁻¹‖ < 1 := by simpa only [norm_neg] using hnorm
  have hlimq := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hlimx : Tendsto (fun n : ℕ => (p⁻¹)^n * x) atTop (𝓝 0) := by
    simpa only [zero_mul] using hlimq.mul_const x
  have hlimf : Tendsto (fun n : ℕ => f ((p⁻¹)^n * x) - c) atTop (𝓝 (f 0 - c)) :=
    (hf.continuousAt.tendsto.comp hlimx).sub_const c
  have hlim := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnormNeg).mul hlimf
  have hconst : Tendsto (fun _ : ℕ => f x - c) atTop (𝓝 0) := by
    simpa only [hiter, zero_mul] using hlim
  have hz : f x - c = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  exact sub_eq_zero.mp hz

theorem solution (p : ℝ) (hp : p > 1)
    (hf : ∀ x : ℝ, 0 < x → ∃ y : ℝ, y + p * y = 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x : ℝ, 0 < x → f x + p * f (p * x) = 1 := by
  refine ⟨fun _ => 1 / (p + 1), continuous_const, ?_⟩
  intro x hx
  have hne : p + 1 ≠ 0 := by linarith
  dsimp
  field_simp
  <;> ring

#print axioms positive_values_unique
#print axioms solution
