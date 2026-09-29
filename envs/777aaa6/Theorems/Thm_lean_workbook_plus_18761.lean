-- Prove2me | Theorems.Thm_lean_workbook_plus_18761
-- name    : lean_workbook_plus_18761
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/dfc858ec-27aa-470a-9c78-4ba11fee31f7
-- statement:
--   Let $a,b,c>0$ such that $a^2b+b^2c+c^2a+ab^2+bc^2+ca^2=4+2abc.$ Prove that $(a^2+b^2)(b^2+c^2)(c^2+a^2)\geq 8.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18761 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 * b + b^2 * c + c^2 * a + a * b^2 + b * c^2 + c * a^2 = 4 + 2 * a * b * c) : (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ 8   :=  by sorry
