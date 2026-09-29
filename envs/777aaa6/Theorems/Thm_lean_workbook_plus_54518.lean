-- Prove2me | Theorems.Thm_lean_workbook_plus_54518
-- name    : lean_workbook_plus_54518
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d4d0ad63-aa23-4ff5-b384-460b0865af18
-- statement:
--   If $a^2+b^2+c^2=3$ , \n $\frac{a^2+b^4}{a+b^2}+\frac{b^2+c^4}{b+c^2}+\frac{c^2+a^4}{c+a^2} \geq 3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54518 : a^2 + b^2 + c^2 = 3 → a^2 + b^4 / (a + b^2) + b^2 + c^4 / (b + c^2) + c^2 + a^4 / (c + a^2) ≥ 3   :=  by sorry
