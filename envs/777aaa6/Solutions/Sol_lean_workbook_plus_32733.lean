-- Prove2me | solution 1 for lean_workbook_plus_32733
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:45:36.263151+00:00
-- url     : https://prove2.me/submissions/a5765605-21d0-4b9c-a5d2-da6a90d45eb8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (k : ℕ) : ¬ ∃ x : ℕ, k^2 < x^2 ∧ x^2 < (k + 1)^2 := by
  rintro ⟨x, h1, h2⟩
  have hx : x ≤ k := by nlinarith
  nlinarith
