-- Prove2me | Theorems.Thm_lean_workbook_plus_81921
-- name    : lean_workbook_plus_81921
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3e68da32-5dc7-42f7-a47b-43db17e995a9
-- statement:
--   Let $ a,b,c,d $ non-negative real numbers and sum of $ a,b,c,d $ equal $4.$ Prove that $(a+b+c+d)^2\geqslant4(ab+bc+cd+da)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81921 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4) : (a + b + c + d) ^ 2 ≥ 4 * (a * b + b * c + c * d + d * a)   :=  by sorry
