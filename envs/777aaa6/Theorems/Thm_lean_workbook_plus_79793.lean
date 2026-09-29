-- Prove2me | Theorems.Thm_lean_workbook_plus_79793
-- name    : lean_workbook_plus_79793
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b0bbd192-c40d-4889-8357-914d525dcaf4
-- statement:
--   If $x\le 1$, prove that $x^{4}-x^{3}+x^{2}-x+1>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79793 (x : ℝ) (hx : x ≤ 1) : x^4 - x^3 + x^2 - x + 1 > 0   :=  by sorry
