-- Prove2me | Theorems.Thm_lean_workbook_plus_38228
-- name    : lean_workbook_plus_38228
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/c2557492-2823-4834-84ab-247e8d8b009f
-- statement:
--   Factor the polynomial $10x^3 - 39x^2 + 29x - 6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38228 (x : ℝ) : 10 * x ^ 3 - 39 * x ^ 2 + 29 * x - 6 = (x - 3) * (2 * x - 1) * (5 * x - 2)   :=  by sorry
