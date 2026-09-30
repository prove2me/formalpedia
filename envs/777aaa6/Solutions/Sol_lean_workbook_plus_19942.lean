-- Prove2me | solution 1 for lean_workbook_plus_19942
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:16.700648+00:00
-- url     : https://prove2.me/submissions/7d1e3ef8-71d5-44f3-ac31-53cc0631af7e

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => x^2 - 2) : ∃ x, x ∈ Set.Icc 0 2 ∧ f x = 0   := by
  refine ⟨Real.sqrt 2, ⟨Real.sqrt_nonneg 2, ?_⟩, ?_⟩
  · exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  · rw [hf]
    norm_num [Real.sq_sqrt]

#print axioms solution
