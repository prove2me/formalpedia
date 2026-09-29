-- Prove2me | solution 1 for mme_dwz_global_behrend_retained_count_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T18:16:34.77604+00:00
-- url     : https://prove2.me/submissions/5cac3ad5-a2c5-409a-9077-870902a984e0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (p A n : ℕ) (S : Finset ℕ) (E D : ℝ)
    (hppos : 0 < p) (hD : 0 < D)
    (hprime : (p : ℝ) * E ≤ 16 * D * (A : ℝ))
    (hbehrend :
      ((p / 2 : ℕ) : ℝ) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
        (S.card : ℝ))
    (hretained :
      ((A : ℝ) * (S.card : ℝ)) / (2 * (p : ℝ) ^ 2) ≤ (n : ℝ)) :
    E *
        (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))))) /
        (32 * D) ≤
      (n : ℝ) := by
  let f : ℝ := ((p / 2 : ℕ) : ℝ)
  let b : ℝ := Real.exp (-4 * Real.sqrt (Real.log f))
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  have hD16 : (0 : ℝ) < 16 * D := mul_pos (by norm_num) hD
  have hf : 0 ≤ f := by positivity
  have hb : 0 < b := Real.exp_pos _
  have hdiv : E / (16 * D) ≤ (A : ℝ) / (p : ℝ) := by
    apply (div_le_div_iff₀ hD16 hpR).2
    nlinarith
  have hscaleNonneg : 0 ≤ f * b / (2 * (p : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hdiv hscaleNonneg
  have hbehrend' : f * b ≤ (S.card : ℝ) := by
    simpa only [f, b] using hbehrend
  have hbucket :
      (A : ℝ) * (f * b) / (2 * (p : ℝ) ^ 2) ≤ (n : ℝ) := by
    calc
      (A : ℝ) * (f * b) / (2 * (p : ℝ) ^ 2) ≤
          (A : ℝ) * (S.card : ℝ) / (2 * (p : ℝ) ^ 2) := by
        gcongr
      _ ≤ (n : ℝ) := hretained
  have hfinal : E * (((f / (p : ℝ)) * b) / (32 * D)) ≤ (n : ℝ) := by
    calc
      E * (((f / (p : ℝ)) * b) / (32 * D)) =
          (E / (16 * D)) * (f * b / (2 * (p : ℝ))) := by
        field_simp
        ring
      _ ≤ ((A : ℝ) / (p : ℝ)) *
          (f * b / (2 * (p : ℝ))) := hscaled
      _ = (A : ℝ) * (f * b) / (2 * (p : ℝ) ^ 2) := by
        field_simp
      _ ≤ (n : ℝ) := hbucket
  dsimp only [f, b] at hfinal
  convert hfinal using 1
  ring
