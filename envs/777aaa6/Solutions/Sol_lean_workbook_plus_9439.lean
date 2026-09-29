-- Prove2me | solution 1 for lean_workbook_plus_9439
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:08.449115+00:00
-- url     : https://prove2.me/submissions/d52201b1-204d-4d0a-b2f9-494d3af306b0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {r p : ℝ} : (∃ q, 2 * r + p = q) ∧ (∃ q, r ^ 2 + 2 * r * p = q) ∧ (∃ q, r ^ 2 * p = q) → ∃ q, r = q ∧ ∃ q, p = q := by
  norm_num
