-- Prove2me | Theorems.Thm_lean_workbook_plus_79854
-- name    : lean_workbook_plus_79854
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/27bd03c0-c328-4ea9-bc49-64ae4d1235d6
-- statement:
--   Let $a,b,c >0$ and $a^2+b^2+c^2 +3= 2(ab+bc+ca).$ Prove that $abc\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79854 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 + 3 = 2 * (a * b + b * c + c * a)) : a * b * c ≥ 1   :=  by sorry
