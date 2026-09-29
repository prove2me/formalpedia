-- Prove2me | Theorems.Thm_lean_workbook_plus_75830
-- name    : lean_workbook_plus_75830
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/230f4a88-24ee-49f8-97b4-bbfc7281800e
-- statement:
--   We want prove $$(a+b+c)^2 \ge abc(a+b+c)+2(a^2b+b^2c+c^2a)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75830 : ∀ a b c : ℝ, (a+b+c)^2 ≥ a*b*c*(a+b+c) + 2 * (a^2 * b + b^2 * c + c^2 * a)   :=  by sorry
