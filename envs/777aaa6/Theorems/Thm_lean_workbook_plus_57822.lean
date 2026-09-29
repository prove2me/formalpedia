-- Prove2me | Theorems.Thm_lean_workbook_plus_57822
-- name    : lean_workbook_plus_57822
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/80bbdd8a-0816-45f4-a106-7b22e9d6f4c0
-- statement:
--   Prove $64y^3+8y+28 \ge 100y^2$ for $y \ge \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57822 (y : ℝ) (hy : y ≥ 1/2) : 64*y^3 + 8*y + 28 ≥ 100*y^2   :=  by sorry
