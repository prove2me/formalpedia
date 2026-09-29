-- Prove2me | Theorems.Thm_lean_workbook_plus_17783
-- name    : lean_workbook_plus_17783
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/e80fa94a-6ca0-408e-93bc-d3f680ab8879
-- statement:
--   Solve for $y$ in the equation $7 = x^3 + 3xy$ given $x=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17783 (x y : ℝ) (hx : x = 1) : 7 = x^3 + 3 * x * y ↔ y = 2   :=  by sorry
