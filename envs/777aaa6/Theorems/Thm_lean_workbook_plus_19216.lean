-- Prove2me | Theorems.Thm_lean_workbook_plus_19216
-- name    : lean_workbook_plus_19216
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/28f2ecc8-6c5d-4a4d-bdc8-5b1c86af5fe1
-- statement:
--   Prove that for all positive real x, $3+x^4\geq 4x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19216 (x : ℝ) (hx : 0 < x) : 3 + x ^ 4 ≥ 4 * x   :=  by sorry
