-- Prove2me | Theorems.Thm_lean_workbook_plus_7050
-- name    : lean_workbook_plus_7050
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/26c9b5e8-454b-415f-9527-a9971ea47a67
-- statement:
--   If a+b+c>=3, show that: $a^2+b^2+c^2+ab+ac+bc\ge6.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7050 (a b c : ℝ) (hab : a + b + c ≥ 3) : a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c ≥ 6   :=  by sorry
