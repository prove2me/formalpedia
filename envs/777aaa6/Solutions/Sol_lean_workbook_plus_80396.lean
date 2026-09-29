-- Prove2me | solution 1 for lean_workbook_plus_80396
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:20:53.432948+00:00
-- url     : https://prove2.me/submissions/4b94522e-53c9-4d7d-843d-04e775d16574

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (k : ℕ) (h : 0 < k) : ∀ n : ℕ, ∃ x y : ℚ, x ^ 2 + y ^ 2 = k ^ 2 := by
  intro n
  exact ⟨k, 0, by norm_num⟩
