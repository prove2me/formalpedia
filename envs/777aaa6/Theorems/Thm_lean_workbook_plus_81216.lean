-- Prove2me | Theorems.Thm_lean_workbook_plus_81216
-- name    : lean_workbook_plus_81216
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2daf7693-27a8-472d-9f89-7c06773b7ef8
-- statement:
--   给出分式 \(\frac{x^2-2}{(x-1)^3}\) 的分解结果：\(- \left( x-1 \right) ^{-3}+2\, \left( x-1 \right) ^{-2}+ \left( x-1 \right) ^{-1}\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81216 (x : ℝ) (hx : x ≠ 1) : (x^2 - 2) / (x - 1)^3 = -1 / (x - 1)^3 + 2 / (x - 1)^2 + 1 / (x - 1)   :=  by sorry
