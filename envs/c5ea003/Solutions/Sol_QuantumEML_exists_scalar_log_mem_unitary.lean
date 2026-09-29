-- Prove2me | solution 1 for QuantumEML.exists_scalar_log_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T10:50:22.242063+00:00
-- url     : https://prove2.me/submissions/70a4d8a2-ee2c-4ff0-9444-280b095585a6

import Mathlib
import Definitions.Def_NumberTheory_EMLQuantumScalarLog
open Complex QuantumEML in
theorem solution :
    ∃ t : ℝ, t ≠ 0 ∧ Complex.log (1 + (t : ℂ) * I) ∈ unitary ℂ := by
  -- `f t = ‖log (1 + t i)‖` is continuous (the argument stays in the right half-plane)
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = ‖Complex.log (1 + (t : ℂ) * I)‖ := ⟨_, fun _ => rfl⟩
  have hcont : Continuous f := by
    have : f = fun t : ℝ => ‖Complex.log (1 + (t : ℂ) * I)‖ := funext hf
    rw [this]
    refine continuous_norm.comp (Continuous.clog (by fun_prop) (fun t => ?_))
    rw [mem_slitPlane_iff]
    left
    simp
  have hf0 : f 0 = 0 := by simp [hf]
  -- `f 3 ≥ Re log (1 + 3i) = (log 10)/2 > 1` since `e² < 10`
  have hf3 : 1 < f 3 := by
    have hnorm : ‖(1 : ℂ) + ((3 : ℝ) : ℂ) * I‖ = Real.sqrt 10 := by
      rw [norm_eq_sqrt_sq_add_sq]
      congr 1
      simp
      norm_num
    have hre : (Complex.log (1 + ((3 : ℝ) : ℂ) * I)).re = Real.log 10 / 2 := by
      rw [Complex.log_re, hnorm, Real.log_sqrt (by norm_num)]
    have h10 : 2 < Real.log 10 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have he := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h2]
      nlinarith [Real.exp_pos 1]
    rw [hf]
    calc (1 : ℝ) < Real.log 10 / 2 := by linarith
      _ = (Complex.log (1 + ((3 : ℝ) : ℂ) * I)).re := hre.symm
      _ ≤ |(Complex.log (1 + ((3 : ℝ) : ℂ) * I)).re| := le_abs_self _
      _ ≤ ‖Complex.log (1 + ((3 : ℝ) : ℂ) * I)‖ := abs_re_le_norm _
  -- the intermediate value theorem on `[0, 3]`
  obtain ⟨t, -, hft⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 3) hcont.continuousOn
    ⟨by rw [hf0]; norm_num, hf3.le⟩
  refine ⟨t, ?_, ?_⟩
  · rintro rfl
    rw [hf0] at hft
    norm_num at hft
  · have hn : ‖Complex.log (1 + (t : ℂ) * I)‖ = 1 := by rw [← hf]; exact hft
    rw [Unitary.mem_iff, star_def, conj_mul', mul_conj', hn]
    norm_num
