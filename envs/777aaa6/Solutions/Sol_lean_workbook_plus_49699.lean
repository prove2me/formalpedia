-- Prove2me | solution 1 for lean_workbook_plus_49699
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:16.863513+00:00
-- url     : https://prove2.me/submissions/c021a9b6-63ee-4843-bd8c-e957eb9a35c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 2^5 * 2^10 * 5^10 * 15^5 = 2^5 * 2^10 * 5^10 * 15^5) : 2^5 * 2^10 * 5^10 * 15^5 = 2^5 * 2^10 * 5^10 * 15^5 := by
  norm_num
