-- Prove2me | solution 1 for lean_workbook_plus_26482
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T19:36:54.328254+00:00
-- url     : https://prove2.me/submissions/80fd019b-746d-49f2-84d7-eb4ab326981e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (N : ℤ) : ∃ x r : ℤ, N = 180 * x + r ∧ 0 ≤ r ∧ r ≤ 179   := by
  refine ⟨N / 180, N % 180, ?_⟩
  omega
