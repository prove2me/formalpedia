-- Prove2me | Theorems.Thm_lean_workbook_plus_17600
-- name    : lean_workbook_plus_17600
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/88ed5cc7-73be-4a98-b58e-0bac5454e797
-- statement:
--   If $x\ge 1$, prove that $x^{4}-x^{3}+x^{2}-x+1>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17600 (x : ℝ) (hx : 1 ≤ x) : x^4 - x^3 + x^2 - x + 1 > 0   :=  by sorry
