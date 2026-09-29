-- Prove2me | Theorems.Thm_lean_workbook_plus_27881
-- name    : lean_workbook_plus_27881
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/ef681e94-4690-4a62-890a-93e88b48df22
-- statement:
--   Prove $8x^3-25x^2+4x+28 \ge 0$ for $x \ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27881 (x:ℝ) (hx: x >= 1): 8*x^3 - 25*x^2 + 4*x + 28 >= 0   :=  by sorry
