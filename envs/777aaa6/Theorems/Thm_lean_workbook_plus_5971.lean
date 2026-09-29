-- Prove2me | Theorems.Thm_lean_workbook_plus_5971
-- name    : lean_workbook_plus_5971
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0e271c31-e2ac-4e52-bcb7-32066204b354
-- statement:
--   $- \left( b+d \right) \left( c+a \right) \left( acd+abd+abc+bcd \right) + \left( a+b+c+d \right) \left( ab+cd \right) \left( bc+ad \right) = \left( a-c \right) ^{2}bcd+ \left( b-d \right) ^{2}acd+ \left( c-a \right) ^{2}abd+ \left( d-b \right) ^{2}abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5971 (a b c d : ℝ) :
  -(b + d) * (c + a) * (a * c * d + a * b * d + a * b * c + b * c * d) + (a + b + c + d) * (a * b + c * d) * (b * c + a * d) =
  (a - c) ^ 2 * b * c * d + (b - d) ^ 2 * a * c * d + (c - a) ^ 2 * a * b * d + (d - b) ^ 2 * a * b * c   :=  by sorry
