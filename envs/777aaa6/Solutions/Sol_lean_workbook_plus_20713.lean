-- Prove2me | solution 1 for lean_workbook_plus_20713
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:43.447891+00:00
-- url     : https://prove2.me/submissions/8733582c-5473-44db-911f-dc25e02db0fd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * a * c + 2 * b * c := by
  (intros; linarith)
