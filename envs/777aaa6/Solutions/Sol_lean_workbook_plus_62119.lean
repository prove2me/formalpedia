-- Prove2me | solution 1 for lean_workbook_plus_62119
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:17.814589+00:00
-- url     : https://prove2.me/submissions/622853de-acd3-4c1b-b146-7f42780ec533

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (α γ : ℝ) (h₁ : 1 / 2 ≤ α ∧ α ≤ γ) (h₂ : γ ≤ 1) : 1 / 2 ≤ α ∧ α ≤ γ ∧ γ ≤ 1 := by
  (intros; simp_all)
