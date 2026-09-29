-- Prove2me | Theorems.Thm_lean_workbook_plus_24283
-- name    : lean_workbook_plus_24283
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/5ad05c0c-8aed-4228-b836-edbfe3de6664
-- statement:
--   Prove that in any triangle with angles A, B, and C, the following equation holds:\n\\(\\sin^2A + \\sin^2B + \\sin^2C = 2(1 + \\cosA \\cosB \\cosC)\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24283 (A B C : ℝ) (hx: A + B + C = π) : (sin A)^2 + (sin B)^2 + (sin C)^2 = 2*(1 + cos A * cos B * cos C)   :=  by sorry
