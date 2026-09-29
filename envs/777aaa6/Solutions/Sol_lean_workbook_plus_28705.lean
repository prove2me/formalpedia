-- Prove2me | solution 1 for lean_workbook_plus_28705
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:19.271458+00:00
-- url     : https://prove2.me/submissions/d9660372-7b1c-4428-a5cc-c23b41605767

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c d : ℝ} (h : a^2 + b^2 + (a - b)^2 = c^2 + d^2 + (c - d)^2) : a^4 + b^4 + (a - b)^4 = c^4 + d^4 + (c - d)^4 := by
  (intros; nlinarith)
