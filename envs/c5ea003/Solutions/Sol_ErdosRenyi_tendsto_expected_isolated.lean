-- Prove2me | solution 1 for ErdosRenyi.tendsto_expected_isolated
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:17:53.3758+00:00
-- url     : https://prove2.me/submissions/e6314c62-dfbc-4c34-a29e-d82ed1c4d0c7

import Mathlib
import Definitions.Def_Probability_NumberTheory_ErdosRenyiThreshold

open Finset BigOperators Filter Topology ErdosRenyi in
theorem solution (c : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - (Real.log n + c) / n) ^ (n - 1)) atTop
      (𝓝 (Real.exp (-c))) := by
  set x : ℕ → ℝ := fun n => (Real.log n + c) / n with hxdef
  -- `(log n)^k / n → 0`
  have hT : ∀ k : ℕ, Tendsto (fun n : ℕ => Real.log n ^ k / n) atTop (𝓝 0) := by
    intro k
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr fun n => ?_
    simp
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hx : Tendsto x atTop (𝓝 0) := by
    have h := (hT 1).add (hinv.const_mul c)
    rw [mul_zero, add_zero] at h
    refine h.congr fun n => ?_
    simp only [hxdef, pow_one]
    ring
  have hx2 : Tendsto (fun n : ℕ => (Real.log n + c) ^ 2 / n) atTop (𝓝 0) := by
    have h := ((hT 2).add ((hT 1).const_mul (2 * c))).add (hinv.const_mul (c ^ 2))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun n => ?_
    ring
  -- eventually `n ≥ 1`, `log n + c > 0`, `x n ≤ 1/2`
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 0 < Real.log n + c ∧ x n ≤ 1 / 2 := by
    have h1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    have h2 : ∀ᶠ n : ℕ in atTop, 0 < Real.log n + c := by
      have := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (-c))
      exact this.mono fun n hn => by simp only [Function.comp] at hn; linarith
    have h3 : ∀ᶠ n : ℕ in atTop, x n ≤ 1 / 2 :=
      hx.eventually (eventually_le_nhds (by norm_num))
    exact ((h1.and h2).and h3).mono fun n h => ⟨h.1.1, h.1.2, h.2⟩
  let g : ℕ → ℝ := fun n => Real.log n + ((n - 1 : ℕ) : ℝ) * Real.log (1 - x n)
  have hfg : ∀ᶠ n : ℕ in atTop,
      Real.exp (g n) = (n : ℝ) * (1 - (Real.log n + c) / n) ^ (n - 1) := by
    filter_upwards [hev] with n hn
    obtain ⟨hn1, hpos, hle⟩ := hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1x : 0 < 1 - x n := by linarith
    have h1x' : 0 < 1 - (Real.log n + c) / n := h1x
    simp only [g, hxdef]
    rw [Real.exp_add, Real.exp_log hnpos, ← Real.log_pow, Real.exp_log (pow_pos h1x' _)]
  -- `log(1-x)` is squeezed between `-(x + 2x²)` and `-x`
  have hbounds : ∀ᶠ n : ℕ in atTop,
      (-c + x n) - 2 * ((Real.log n + c) ^ 2 / n) ≤ g n ∧ g n ≤ -c + x n := by
    filter_upwards [hev] with n hn
    obtain ⟨hn1, hpos, hle⟩ := hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hxpos : 0 < x n := div_pos hpos hnpos
    have h1x : 0 < 1 - x n := by linarith
    have hcast : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
    have hm : (0 : ℝ) ≤ n - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    have hup : Real.log (1 - x n) ≤ -x n := by linarith [Real.log_le_sub_one_of_pos h1x]
    have hlow : -(x n + 2 * x n ^ 2) ≤ Real.log (1 - x n) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.2 h1x)
      rw [Real.log_inv] at h
      have hq : (1 - x n)⁻¹ - 1 ≤ x n + 2 * x n ^ 2 := by
        rw [inv_eq_one_div, div_sub_one h1x.ne', div_le_iff₀ h1x]
        nlinarith
      linarith
    have hU : Real.log n - (n - 1) * x n = -c + x n := by
      simp only [hxdef]
      field_simp
      ring
    have hsq : (n : ℝ) * x n ^ 2 = (Real.log n + c) ^ 2 / n := by
      simp only [hxdef]
      field_simp
    simp only [g]
    rw [hcast]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hlow hm, sq_nonneg (x n)]
    · nlinarith [mul_le_mul_of_nonneg_left hup hm]
  have hg : Tendsto g atTop (𝓝 (-c)) := by
    have hU : Tendsto (fun n : ℕ => -c + x n) atTop (𝓝 (-c)) := by
      simpa using hx.const_add (-c)
    have hL : Tendsto (fun n : ℕ => (-c + x n) - 2 * ((Real.log n + c) ^ 2 / n)) atTop
        (𝓝 (-c)) := by
      simpa using hU.sub (hx2.const_mul 2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU (hbounds.mono fun n h => h.1)
      (hbounds.mono fun n h => h.2)
  exact ((Real.continuous_exp.tendsto _).comp hg).congr' hfg
