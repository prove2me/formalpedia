-- Prove2me | solution 1 for lean_workbook_plus_42472
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:17.213265+00:00
-- url     : https://prove2.me/submissions/d2c825c9-cdfe-486d-a7e9-c9bb3817a491

import Mathlib.Analysis.Complex.Basic

theorem solution  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 2) :
  0 < x ∧ x < 2 := ⟨h₀, h₁⟩
