-- Prove2me | Theorems.Thm_lean_workbook_plus_30097
-- name    : lean_workbook_plus_30097
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b73dda73-f538-4f8a-be6f-dfe22e9ea58a
-- statement:
--   Let $a\ge 1,b\ge 2,c\ge 3,ab+bc+ca=16,$ prove that $abc\le 12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30097 (a b c : ℝ) (hab : 1 ≤ a) (hbc : 2 ≤ b) (hca : 3 ≤ c) (habc : a * b + b * c + c * a = 16) : a * b * c ≤ 12   :=  by sorry
