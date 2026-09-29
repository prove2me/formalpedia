-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.localExp_mix_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:38:27.35772+00:00
-- url     : https://prove2.me/submissions/af2eb9e6-1013-4fd1-931e-94d499c47127

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter HarmonicBulkSteeperEdge in
theorem solution {w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) {k : ℕ}
    (hk : 1 ≤ k) :
    localExp (mix w a b) k ≤ a + (w / (1 - w)) * (b - a) * (k : ℝ) ^ (-(b - a)) := by
  have hX : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hX1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  set t : ℝ := Real.log (((k : ℝ) + 1) / (k : ℝ)) with ht
  have htpos : 0 < t := Real.log_pos (by rw [lt_div_iff₀ hX]; linarith)
  have hpow : ∀ c : ℝ, ((k : ℝ) + 1) ^ (-c) = (k : ℝ) ^ (-c) * Real.exp (-c * t) := by
    intro c
    rw [Real.rpow_def_of_pos hX1, Real.rpow_def_of_pos hX, ← Real.exp_add, ht,
      Real.log_div hX1.ne' hX.ne']
    congr 1
    ring
  set p : ℝ := (1 - w) * (k : ℝ) ^ (-a) with hp
  set s : ℝ := w * (k : ℝ) ^ (-b) with hs
  have hppos : 0 < p := mul_pos (by linarith) (Real.rpow_pos_of_pos hX _)
  have hspos : 0 < s := mul_pos hw0 (Real.rpow_pos_of_pos hX _)
  have hmk : mix w a b k = p + s := by
    simp only [mix, pw, hp, hs]
  have hmk1 : mix w a b (k + 1) = p * Real.exp (-a * t) + s * Real.exp (-b * t) := by
    simp only [mix, pw, hp, hs]
    push_cast
    rw [hpow a, hpow b]
    ring
  have hD : 0 < p * Real.exp (-a * t) + s * Real.exp (-b * t) := by
    have := Real.exp_pos (-a * t)
    have := Real.exp_pos (-b * t)
    positivity
  have hloc : localExp (mix w a b) k
      = Real.log ((p + s) / (p * Real.exp (-a * t) + s * Real.exp (-b * t))) / t := by
    unfold localExp
    rw [hmk, hmk1]
  have hRpos : 0 < (p + s) / (p * Real.exp (-a * t) + s * Real.exp (-b * t)) :=
    div_pos (by linarith) hD
  have e1 : Real.exp (a * t) * Real.exp (-a * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hupper : localExp (mix w a b) k ≤ a + (w / (1 - w)) * (b - a) * (k : ℝ) ^ (-(b - a)) := by
    have hka : (k : ℝ) ^ (-(b - a)) = (k : ℝ) ^ (-b) / (k : ℝ) ^ (-a) := by
      rw [← Real.rpow_sub hX]
      congr 1
      ring
    have hsp : s / p = w / (1 - w) * (k : ℝ) ^ (-(b - a)) := by
      rw [hka, div_mul_div_comm]
    have hEa : Real.exp (a * t) * Real.exp (-b * t) = Real.exp (-(b - a) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hEge : 1 - (b - a) * t ≤ Real.exp (-(b - a) * t) := by
      have := Real.add_one_le_exp (-(b - a) * t)
      linarith
    have hx0 : 0 ≤ s / p * (b - a) * t :=
      mul_nonneg (mul_nonneg (div_pos hspos hppos).le (by linarith)) htpos.le
    have hxp : s / p * (b - a) * t * p = s * (b - a) * t := by
      field_simp
    have hRle : (p + s) / (p * Real.exp (-a * t) + s * Real.exp (-b * t))
        ≤ Real.exp (a * t) * (1 + s / p * (b - a) * t) := by
      rw [div_le_iff₀ hD]
      have hexp : Real.exp (a * t) * (1 + s / p * (b - a) * t)
            * (p * Real.exp (-a * t) + s * Real.exp (-b * t))
          = (1 + s / p * (b - a) * t) * (p + s * Real.exp (-(b - a) * t)) := by
        linear_combination (1 + s / p * (b - a) * t) * p * e1
          + (1 + s / p * (b - a) * t) * s * hEa
      rw [hexp]
      have h1 := mul_le_mul_of_nonneg_left hEge hspos.le
      have h2 : 0 ≤ s / p * (b - a) * t * s * Real.exp (-(b - a) * t) :=
        mul_nonneg (mul_nonneg hx0 hspos.le) (Real.exp_pos _).le
      nlinarith
    have hlog : Real.log ((p + s) / (p * Real.exp (-a * t) + s * Real.exp (-b * t)))
        ≤ a * t + s / p * (b - a) * t := by
      calc Real.log ((p + s) / (p * Real.exp (-a * t) + s * Real.exp (-b * t)))
          ≤ Real.log (Real.exp (a * t) * (1 + s / p * (b - a) * t)) := Real.log_le_log hRpos hRle
        _ = a * t + Real.log (1 + s / p * (b - a) * t) := by
            rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp]
        _ ≤ a * t + s / p * (b - a) * t := by
            have := Real.log_le_sub_one_of_pos (show 0 < 1 + s / p * (b - a) * t by linarith)
            linarith
    rw [hloc, div_le_iff₀ htpos]
    have hc : w / (1 - w) * (b - a) * (k : ℝ) ^ (-(b - a)) = s / p * (b - a) := by
      rw [hsp]
      ring
    rw [hc]
    nlinarith
  exact hupper
