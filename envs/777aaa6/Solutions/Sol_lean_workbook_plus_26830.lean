-- Prove2me | solution 1 for lean_workbook_plus_26830
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:44.159998+00:00
-- url     : https://prove2.me/submissions/d89383d0-6433-496c-8d2a-c6b0c81fabdc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (S : Finset ℚ) (hS : ∀ q : ℚ, q ∈ S ↔ q.den ≤ 2009 ∧ q < 1257 / 2009) : (∀ q : ℚ, q ∈ S → q.den ≤ 2009 ∧ q < 1257 / 2009) ∧ (∀ q : ℚ, q.den ≤ 2009 ∧ q < 1257 / 2009 → q ∈ S) := by
  (intros; simp_all)
