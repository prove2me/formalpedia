-- Prove2me | solution 1 for lean_workbook_plus_74935
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:36:17.807995+00:00
-- url     : https://prove2.me/submissions/809925a7-295c-433f-85c4-359f419b933b

import Mathlib.Data.Real.Basic

private theorem no_surjective_product_one (f g : ℝ → ℝ)
    (hf : Function.Surjective f) : ¬ ∀ x : ℝ, f x * g x = 1 := by
  intro h
  obtain ⟨x, hx⟩ := hf 0
  have hbad := h x
  rw [hx, zero_mul] at hbad
  exact zero_ne_one hbad

theorem solution : ¬∃ f : ℝ → ℝ,
    Function.Bijective f ∧ ∀ x : ℝ, f x * f⁻¹ x = 1 := by
  rintro ⟨f, hf, h⟩
  exact no_surjective_product_one f f⁻¹ hf.2 h
