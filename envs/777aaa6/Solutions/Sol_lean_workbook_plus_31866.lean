-- Prove2me | solution 1 for lean_workbook_plus_31866
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:47.145062+00:00
-- url     : https://prove2.me/submissions/cf007b74-c185-4889-868c-d7c654739cf0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : ((n:ℝ) / (n + 1))^(n^2) = (1 - (1 / (n + 1)))^(n^2) := by
  (intros; field_simp; ring)
