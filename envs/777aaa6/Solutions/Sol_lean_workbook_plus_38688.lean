-- Prove2me | solution 1 for lean_workbook_plus_38688
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:38:43.860596+00:00
-- url     : https://prove2.me/submissions/58235b75-a766-4485-aa8b-755dd2256aa7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q r : ℤ) : p * q * r + (p + q) * (q + r) * (r + p) = (p + q + r) * (p * q + q * r + r * p) := by
  (intros; linarith)
