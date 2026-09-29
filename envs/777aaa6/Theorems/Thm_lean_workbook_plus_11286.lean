-- Prove2me | Theorems.Thm_lean_workbook_plus_11286
-- name    : lean_workbook_plus_11286
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/dda6a99c-6112-4dd2-bfcc-4a4a6a21e347
-- statement:
--   Prove that $2(x-\frac{3}{4})^2+\frac{1}{x+1}\geq \frac{1}{8}$ for $x\in [0,\infty [$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11286 (x : ℝ) (hx: x ≥ 0) : 2 * (x - 3 / 4) ^ 2 + 1 / (x + 1) ≥ 1 / 8   :=  by sorry
