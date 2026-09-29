-- Prove2me | solution 1 for lean_workbook_plus_13495
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:05.435518+00:00
-- url     : https://prove2.me/submissions/c1d9d644-d8c0-4876-99f1-9bcc4646db34

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r s a d : ℤ) : (r + s) ^ 3 = (a + d) ^ 3 → r ^ 3 + s ^ 3 = a ^ 3 + d ^ 3 + 3 * a ^ 2 * d + 3 * a * d ^ 2 - 3 * r * s * (r + s) := by
  (intros; linarith)
