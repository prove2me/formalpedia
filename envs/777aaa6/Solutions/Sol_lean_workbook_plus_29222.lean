-- Prove2me | solution 1 for lean_workbook_plus_29222
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:29.438871+00:00
-- url     : https://prove2.me/submissions/45c16c17-78ce-48cf-af0e-244cd5a53ae7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 1 ≤ 1 ∧ 4 ≤ 4) (h₂ : 2 ≤ 2 ∧ 3 ≤ 3) (h₃ : 3 ≤ 3 ∧ 2 ≤ 2) (h₄ : 4 ≤ 4 ∧ 1 ≤ 1) : 1 * 4 + 2 * 3 + 3 * 2 + 4 * 1 = 20 := by
  norm_num
