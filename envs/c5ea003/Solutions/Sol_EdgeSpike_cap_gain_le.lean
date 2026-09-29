-- Prove2me | solution 1 for EdgeSpike.cap_gain_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T07:11:47.183485+00:00
-- url     : https://prove2.me/submissions/3965bf97-7cf4-4fbd-a8b7-fcccddc4ccf5

import Mathlib
import Definitions.Def_MachineLearning_EdgeSpikeCensoring

open EdgeSpike Real in
theorem solution {h rho t b : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hb : 1 ≤ b) :
    binLogLik h (edgeProbLimit rho t) - binLogLik h (edgeProb rho t b) ≤
      (2 * rho / min ((1 - rho) * t) (1 - edgeProbLimit rho t)) * exp (-(b * t)) := by
  set E := Real.exp (-(b * t)) with hE
  set D := Real.exp (-b) with hD
  have hbt : b * t < b := by nlinarith
  have hE1 : E < 1 := by
    rw [hE, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith)
  have hDE : D < E := Real.exp_lt_exp.2 (by linarith)
  have hD0 : 0 < D := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  -- `e^{-b} ≤ e^{-1} ≤ 1/2`
  have hDhalf : D ≤ 1 / 2 := by
    have h1 : D ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    linarith
  set P := edgeProbLimit rho t with hP
  set Q := edgeProb rho t b with hQ
  have hF : truncExpCDF b t = (1 - E) / (1 - D) := rfl
  have hFnn : 0 ≤ (1 - E) / (1 - D) := div_nonneg (by linarith) (by linarith)
  have hD1 : (1 - D) ≠ 0 := by linarith
  have hgap : P - Q = rho * ((E - D) / (1 - D)) := by
    rw [hP, hQ]
    unfold edgeProbLimit edgeProb
    rw [hF]
    field_simp
    ring
  have hQlo : (1 - rho) * t ≤ Q := by
    rw [hQ]
    unfold edgeProb
    rw [hF]
    nlinarith
  have hpos1 : 0 < (1 - rho) * t := mul_pos (by linarith) ht0
  have hQpos : 0 < Q := lt_of_lt_of_le hpos1 hQlo
  have hgap0 : 0 ≤ P - Q := by
    rw [hgap]
    exact mul_nonneg hrho0.le (div_nonneg (by linarith) (by linarith))
  have hgapE : P - Q ≤ 2 * rho * E := by
    rw [hgap]
    have h1 : (E - D) / (1 - D) ≤ 2 * E := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith
  have hP1 : 1 - P = (1 - rho) * (1 - t) := by
    rw [hP]
    unfold edgeProbLimit
    ring
  have hP1pos : 0 < 1 - P := by
    rw [hP1]
    exact mul_pos (by linarith) (by linarith)
  -- the bulk term only helps the capped model
  have hlog2 : Real.log (1 - P) ≤ Real.log (1 - Q) := Real.log_le_log hP1pos (by linarith)
  have hlog1 : Real.log P - Real.log Q ≤ (P - Q) / Q := by
    have hPpos : 0 < P := by linarith
    rw [← Real.log_div hPpos.ne' hQpos.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hPpos hQpos)
    have h2 : P / Q - 1 = (P - Q) / Q := by
      field_simp
    linarith
  have hlog1nn : 0 ≤ (P - Q) / Q := div_nonneg hgap0 hQpos.le
  have hmin_pos : 0 < min ((1 - rho) * t) (1 - P) := lt_min hpos1 hP1pos
  have hmin_le : min ((1 - rho) * t) (1 - P) ≤ Q := (min_le_left _ _).trans hQlo
  have e : binLogLik h P - binLogLik h Q
      = h * (Real.log P - Real.log Q) + (1 - h) * (Real.log (1 - P) - Real.log (1 - Q)) := by
    unfold binLogLik
    ring
  rw [e]
  have hA : h * (Real.log P - Real.log Q) ≤ (P - Q) / Q := by
    calc h * (Real.log P - Real.log Q) ≤ h * ((P - Q) / Q) := mul_le_mul_of_nonneg_left hlog1 hh0
      _ ≤ 1 * ((P - Q) / Q) := mul_le_mul_of_nonneg_right hh1 hlog1nn
      _ = (P - Q) / Q := one_mul _
  have hB : (1 - h) * (Real.log (1 - P) - Real.log (1 - Q)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hC : (P - Q) / Q ≤ 2 * rho * E / min ((1 - rho) * t) (1 - P) := by
    calc (P - Q) / Q ≤ 2 * rho * E / Q := div_le_div_of_nonneg_right hgapE hQpos.le
      _ ≤ 2 * rho * E / min ((1 - rho) * t) (1 - P) :=
          div_le_div_of_nonneg_left (by positivity) hmin_pos hmin_le
  have hR : 2 * rho / min ((1 - rho) * t) (1 - P) * E = 2 * rho * E / min ((1 - rho) * t) (1 - P) := by
    ring
  rw [hR]
  linarith
