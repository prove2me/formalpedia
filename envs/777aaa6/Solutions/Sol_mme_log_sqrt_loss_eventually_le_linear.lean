-- Prove2me | solution 1 for mme_log_sqrt_loss_eventually_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T23:41:53.294778+00:00
-- url     : https://prove2.me/submissions/bb8002c5-13df-49d7-8d54-59a2f7c36762

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Filter Topology

set_option autoImplicit false
set_option warningAsError true

private theorem log_add_one_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, add_assoc] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hn

private theorem sqrt_add_one_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.sqrt ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt ((n : ℝ) + 1))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have hratio : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / n)
      atTop (𝓝 1) := by
    simpa [add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 0 1
        (d := 1) one_ne_zero)
  have hprod := hratio.mul hinv
  simp only [mul_zero] at hprod
  apply hprod.congr
  intro n
  have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)
  by_cases hnzero : n = 0
  · simp [hnzero]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hnzero
  field_simp [hs, hnr]
  nlinarith [hsq]

/-- Fixed natural-log, square-root and constant losses are eventually
smaller than any prescribed positive linear budget. -/
theorem solution (a b c delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      a * Real.log ((n : ℝ) + 1) + b * Real.sqrt ((n : ℝ) + 1) + c ≤
        (n : ℝ) * delta := by
  have hlim : Tendsto
      (fun n : ℕ ↦
        (a * Real.log ((n : ℝ) + 1) + b * Real.sqrt ((n : ℝ) + 1) + c) /
          (n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      ((log_add_one_div_nat_tendsto_zero.const_mul a).add
        (sqrt_add_one_div_nat_tendsto_zero.const_mul b)).add
        (tendsto_const_div_atTop_nhds_zero_nat c)
  filter_upwards [hlim.eventually_lt_const hdelta, eventually_gt_atTop 0]
    with n hn hnpos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlt := (div_lt_iff₀ hnr).mp hn
  nlinarith
