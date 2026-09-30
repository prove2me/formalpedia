-- Prove2me | solution 1 for RybinAI2026.P01.trigKernel_weight_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:52:22.325278+00:00
-- url     : https://prove2.me/submissions/a56027a6-f614-4dd5-bb29-e4a6acd27725

import Mathlib

open MeasureTheory

theorem solution (w1 w2 : ℝ) (hw1 : 0 ≤ w1) (hw12 : w1 ≤ w2) :
    let K : ℝ → ℝ := fun w =>
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        1 / (1 + 2 * w * Real.sin θ * Real.cos θ)
    K w2 ≤ K w1 ∧ (1 + w1) * K w1 ≤ (1 + w2) * K w2 := by
  let Kfun : ℝ → ℝ := fun w =>
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
      1 / (1 + 2 * w * Real.sin θ * Real.cos θ)
  change Kfun w2 ≤ Kfun w1 ∧ (1 + w1) * Kfun w1 ≤ (1 + w2) * Kfun w2
  have hw2 : 0 ≤ w2 := le_trans hw1 hw12
  have hp : 0 < Real.pi / 2 := by positivity
  have hbox (θ : ℝ) (hθ : θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2)) :
      θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    simpa only [Set.uIcc_of_le hp.le] using hθ
  have htrig (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
      0 ≤ Real.sin θ * Real.cos θ ∧ 2 * Real.sin θ * Real.cos θ ≤ 1 := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [hθ.1, Real.pi_pos]) hθ.2
    constructor
    · exact mul_nonneg hs hc
    · nlinarith [sq_nonneg (Real.sin θ - Real.cos θ), Real.sin_sq_add_cos_sq θ]
  have hdenPos (w : ℝ) (hw : 0 ≤ w) (θ : ℝ)
      (hθ : θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2)) :
      0 < 1 + 2 * w * Real.sin θ * Real.cos θ := by
    have hb := hbox θ hθ
    have ht := htrig θ hb
    have hmul : 0 ≤ 2 * w * (Real.sin θ * Real.cos θ) :=
      mul_nonneg (mul_nonneg (by norm_num) hw) ht.1
    nlinarith [hmul]
  have hcont (w : ℝ) (hw : 0 ≤ w) :
      ContinuousOn (fun θ : ℝ => 1 / (1 + 2 * w * Real.sin θ * Real.cos θ))
        (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    refine continuousOn_const.div (by fun_prop) ?_
    intro θ hθ
    exact ne_of_gt (hdenPos w hw θ hθ)
  have hweightCont (w : ℝ) (hw : 0 ≤ w) :
      ContinuousOn (fun θ : ℝ => (1 + w) /
        (1 + 2 * w * Real.sin θ * Real.cos θ))
        (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    refine continuousOn_const.div (by fun_prop) ?_
    intro θ hθ
    exact ne_of_gt (hdenPos w hw θ hθ)
  constructor
  · change (∫ θ in (0 : ℝ)..(Real.pi / 2),
        1 / (1 + 2 * w2 * Real.sin θ * Real.cos θ)) ≤
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        1 / (1 + 2 * w1 * Real.sin θ * Real.cos θ)
    apply intervalIntegral.integral_mono_on hp.le
      (hcont w2 hw2).intervalIntegrable (hcont w1 hw1).intervalIntegrable
    intro θ hθ
    have ht := htrig θ hθ
    have hd1 := hdenPos w1 hw1 θ (by simpa only [Set.uIcc_of_le hp.le] using hθ)
    have hd2 := hdenPos w2 hw2 θ (by simpa only [Set.uIcc_of_le hp.le] using hθ)
    have hle : 1 + 2 * w1 * Real.sin θ * Real.cos θ ≤
        1 + 2 * w2 * Real.sin θ * Real.cos θ := by
      nlinarith [mul_nonneg (by nlinarith [ht.1] : 0 ≤ 2 * (Real.sin θ * Real.cos θ)) (sub_nonneg.mpr hw12)]
    exact (div_le_div_iff₀ hd2 hd1).2 (by nlinarith [hle])
  · have hpoint (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
        (1 + w1) / (1 + 2 * w1 * Real.sin θ * Real.cos θ) ≤
          (1 + w2) / (1 + 2 * w2 * Real.sin θ * Real.cos θ) := by
      have ht := htrig θ hθ
      have hd1 := hdenPos w1 hw1 θ (by simpa only [Set.uIcc_of_le hp.le] using hθ)
      have hd2 := hdenPos w2 hw2 θ (by simpa only [Set.uIcc_of_le hp.le] using hθ)
      rw [div_le_div_iff₀ hd1 hd2]
      have hprod := mul_nonneg (sub_nonneg.mpr hw12)
        (sub_nonneg.mpr ht.2)
      nlinarith [hprod]
    calc
      (1 + w1) * Kfun w1 =
          ∫ θ in (0 : ℝ)..(Real.pi / 2),
            (1 + w1) / (1 + 2 * w1 * Real.sin θ * Real.cos θ) := by
        dsimp [Kfun]
        rw [← intervalIntegral.integral_const_mul]
        simp only [mul_one_div]
      _ ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2),
            (1 + w2) / (1 + 2 * w2 * Real.sin θ * Real.cos θ) :=
        intervalIntegral.integral_mono_on hp.le
          (hweightCont w1 hw1).intervalIntegrable (hweightCont w2 hw2).intervalIntegrable hpoint
      _ = (1 + w2) * Kfun w2 := by
        dsimp [Kfun]
        rw [← intervalIntegral.integral_const_mul]
        simp only [mul_one_div]


