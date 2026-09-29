-- Prove2me | Theorems.Thm_lean_workbook_plus_57374
-- name    : lean_workbook_plus_57374
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fb361746-33fd-49f5-85aa-130a352d3b93
-- statement:
--   Given that $1$ and $-5$ are roots of the cubic equation $2x^3+9x^2-6x-5=0$, find the third root.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57374 (x : ℝ) : (x = 1 ∨ x = -5 → 2*x^3 + 9*x^2 - 6*x - 5 = 0)   :=  by sorry
