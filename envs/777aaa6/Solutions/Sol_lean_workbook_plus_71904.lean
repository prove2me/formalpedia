-- Prove2me | solution 1 for lean_workbook_plus_71904
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:51.208376+00:00
-- url     : https://prove2.me/submissions/28667977-d9c2-4e74-b47d-069755dbcd30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 5 + (b - c) ^ 5 + (c - a) ^ 5 = 5 * (a - b) * (b - c) * (c - a) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
  (intros; linarith)
