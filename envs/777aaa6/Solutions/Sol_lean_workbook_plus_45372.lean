-- Prove2me | solution 1 for lean_workbook_plus_45372
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:49:42.0058+00:00
-- url     : https://prove2.me/submissions/3c0a9123-f9bb-4f8a-8087-b4941d7a3590

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y)
  (h₁ : Real.sqrt x = Real.sqrt y) :
  x = y := by
  (intros; simp_all)
