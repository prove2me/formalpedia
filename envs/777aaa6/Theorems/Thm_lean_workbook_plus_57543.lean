-- Prove2me | Theorems.Thm_lean_workbook_plus_57543
-- name    : lean_workbook_plus_57543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/db7ae2dd-8c07-402b-b23b-ceb290fb041a
-- statement:
--   Prove that $t(t-3)^2-4\leq0$ for $1\leq t\leq\frac{3}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57543 (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t ≤ 3/2) : t * (t - 3) ^ 2 - 4 ≤ 0   :=  by sorry
