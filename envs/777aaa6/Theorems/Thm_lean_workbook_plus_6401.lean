-- Prove2me | Theorems.Thm_lean_workbook_plus_6401
-- name    : lean_workbook_plus_6401
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/279bf63c-07aa-4bc4-9d3b-95162db7f474
-- statement:
--   If $|x| \geq 1$ and $x^5-x^3 + x - 1 = a$, prove that $x^6 - 1 \geq 2a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6401 (x : ℝ) (a : ℝ) (hx : abs x ≥ 1) (h : x^5 - x^3 + x - 1 = a) :
x^6 - 1 ≥ 2 * a   :=  by sorry
