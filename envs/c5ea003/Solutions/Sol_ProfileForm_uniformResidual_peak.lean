-- Prove2me | solution 1 for ProfileForm.uniformResidual_peak
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:34:07.458041+00:00
-- url     : https://prove2.me/submissions/f046e16f-8701-4850-a66c-e995c64b601a

import Mathlib
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak

open ProfileForm Set in
theorem solution :
    (∃ m ∈ Ioo (3:ℝ) 100, IsMaxOn uniformResidual (Icc (3:ℝ) 100) m) ∧
      ¬ MonotoneOn uniformResidual (Icc (3:ℝ) 100) ∧
      ¬ AntitoneOn uniformResidual (Icc (3:ℝ) 100) := by
  -- closed form on the positive axis
  have hform : ∀ x : ℝ, 0 < x →
      uniformResidual x = x / ((1 + x) ^ (11 / 10 : ℝ) * (1 - Real.exp (-x))) := by
    intro x hx
    have h1 : (0 : ℝ) < 1 + x := by linarith
    have h2 : 0 < 1 - Real.exp (-x) := by
      have : Real.exp (-x) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.2 (by linarith)
      linarith
    unfold uniformResidual powerProfile dickmanMixtureBaseline
    rw [Real.rpow_neg h1.le]
    field_simp
  -- tenth powers of the rational powers
  have hpow : ∀ t : ℝ, 0 ≤ t → (t ^ (11 / 10 : ℝ)) ^ (10 : ℕ) = t ^ (11 : ℕ) := by
    intro t ht
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  set P4 := (4 : ℝ) ^ (11 / 10 : ℝ) with hP4
  set P10 := (10 : ℝ) ^ (11 / 10 : ℝ) with hP10
  set P101 := (101 : ℝ) ^ (11 / 10 : ℝ) with hP101
  have hP4pos : 0 < P4 := by positivity
  have hP10pos : 0 < P10 := by positivity
  have hP101pos : 0 < P101 := by positivity
  have hc1 : P10 < 285 / 100 * P4 := by
    by_contra h
    rw [not_lt] at h
    have h' := pow_le_pow_left₀ (by positivity) h 10
    rw [mul_pow, hpow 4 (by norm_num), hpow 10 (by norm_num)] at h'
    norm_num at h'
  have hc2 : 100 * P10 < 9 * P101 := by
    by_contra h
    rw [not_lt] at h
    have h' := pow_le_pow_left₀ (by positivity) h 10
    rw [mul_pow, mul_pow, hpow 101 (by norm_num), hpow 10 (by norm_num)] at h'
    norm_num at h'
  -- exponential bounds
  have he3 : Real.exp (-3) < 5 / 100 := by
    have h1 := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h20 : (20 : ℝ) < Real.exp 3 := by
      rw [h3]
      have hc := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
      norm_num at hc
      linarith
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 3) (by norm_num)]
    linarith
  have he9 : 0 < Real.exp (-9) := Real.exp_pos _
  have he9lt : Real.exp (-100) < Real.exp (-9) := Real.exp_lt_exp.2 (by norm_num)
  have he100 : 0 < Real.exp (-100) := Real.exp_pos _
  have he9one : Real.exp (-9) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by norm_num)
  -- the three sample values
  have hu3 : uniformResidual 3 = 3 / (P4 * (1 - Real.exp (-3))) := by
    rw [hform 3 (by norm_num)]
    norm_num [hP4]
  have hu9 : uniformResidual 9 = 9 / (P10 * (1 - Real.exp (-9))) := by
    rw [hform 9 (by norm_num)]
    norm_num [hP10]
  have hu100 : uniformResidual 100 = 100 / (P101 * (1 - Real.exp (-100))) := by
    rw [hform 100 (by norm_num)]
    norm_num [hP101]
  have hd3 : 0 < P4 * (1 - Real.exp (-3)) := mul_pos hP4pos (by linarith)
  have hd9 : 0 < P10 * (1 - Real.exp (-9)) := mul_pos hP10pos (by linarith)
  have hd100 : 0 < P101 * (1 - Real.exp (-100)) := mul_pos hP101pos (by linarith)
  have hlt39 : uniformResidual 3 < uniformResidual 9 := by
    rw [hu3, hu9, div_lt_div_iff₀ hd3 hd9]
    have hA : 3 * (P10 * (1 - Real.exp (-9))) ≤ 3 * P10 := by nlinarith
    have hC : 0 < P4 * (45 / 100 - 9 * Real.exp (-3)) := mul_pos hP4pos (by linarith)
    nlinarith
  have hlt1009 : uniformResidual 100 < uniformResidual 9 := by
    rw [hu100, hu9, div_lt_div_iff₀ hd100 hd9]
    have hA : 100 * P10 * (1 - Real.exp (-9)) < 9 * P101 * (1 - Real.exp (-9)) :=
      mul_lt_mul_of_pos_right hc2 (by linarith)
    have hB : 0 < 9 * P101 * (Real.exp (-9) - Real.exp (-100)) :=
      mul_pos (by positivity) (by linarith)
    nlinarith
  -- continuity on the window
  have hcont : ContinuousOn uniformResidual (Icc (3 : ℝ) 100) := by
    have heq : EqOn uniformResidual
        (fun x => x / ((1 + x) ^ (11 / 10 : ℝ) * (1 - Real.exp (-x)))) (Icc (3 : ℝ) 100) :=
      fun x hx => hform x (by linarith [hx.1])
    refine ContinuousOn.congr ?_ heq
    refine continuousOn_id.div (ContinuousOn.mul ?_ ?_) ?_
    · exact (continuousOn_const.add continuousOn_id).rpow_const
        (fun x hx => Or.inl (show (0 : ℝ) < 1 + x by linarith [hx.1]).ne')
    · exact continuousOn_const.sub (Real.continuous_exp.comp_continuousOn continuousOn_neg)
    · intro x hx
      have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
      have h2 : 0 < 1 - Real.exp (-x) := by
        have : Real.exp (-x) < 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.2 (by linarith [hx.1])
        linarith
      positivity
  have h3m : (3 : ℝ) ∈ Icc (3 : ℝ) 100 := ⟨le_rfl, by norm_num⟩
  have h9m : (9 : ℝ) ∈ Icc (3 : ℝ) 100 := ⟨by norm_num, by norm_num⟩
  have h100m : (100 : ℝ) ∈ Icc (3 : ℝ) 100 := ⟨by norm_num, le_rfl⟩
  refine ⟨?_, fun hmono => ?_, fun hanti => ?_⟩
  · obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨3, h3m⟩ hcont
    refine ⟨m, ⟨?_, ?_⟩, hmax⟩
    · rcases eq_or_lt_of_le hm.1 with h | h
      · have := hmax h9m
        rw [← h] at this
        exact absurd this (not_le.2 hlt39)
      · exact h
    · rcases eq_or_lt_of_le hm.2 with h | h
      · have := hmax h9m
        rw [h] at this
        exact absurd this (not_le.2 hlt1009)
      · exact h
  · exact absurd (hmono h9m h100m (by norm_num)) (not_le.2 hlt1009)
  · exact absurd (hanti h3m h9m (by norm_num)) (not_le.2 hlt39)
