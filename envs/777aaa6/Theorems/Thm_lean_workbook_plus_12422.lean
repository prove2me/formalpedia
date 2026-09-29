-- Prove2me | Theorems.Thm_lean_workbook_plus_12422
-- name    : lean_workbook_plus_12422
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/208eaf4e-0ec8-425e-9ae0-ca8cc0118ada
-- statement:
--   Prove that $|x|\le 2\implies \left|\frac{2x^2+3x+2}{x^2+2}\right|\le 8$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12422 (x : ℝ) (hx : |x| ≤ 2) : ‖(2 * x ^ 2 + 3 * x + 2) / (x ^ 2 + 2)‖ ≤ 8   :=  by sorry
