-- Prove2me | Theorems.Thm_lean_workbook_plus_17488
-- name    : lean_workbook_plus_17488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/68fe57bc-99d5-4a21-bd5f-d3e57b657afc
-- statement:
--   Suppose $u+2v>4$, use AM-GM inequality to show that $2uv\leq\frac{u^2+4v^2}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17488 (u v : ℝ) (h : u + 2 * v > 4) : 2 * u * v ≤ (u ^ 2 + 4 * v ^ 2) / 2   :=  by sorry
