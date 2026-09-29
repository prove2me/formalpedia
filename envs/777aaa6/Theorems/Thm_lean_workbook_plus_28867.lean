-- Prove2me | Theorems.Thm_lean_workbook_plus_28867
-- name    : lean_workbook_plus_28867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f3d359c0-7966-4aa7-8aa7-da1623be9f54
-- statement:
--   Given $a=6$ and $b=2$, find $\sqrt{a}-\sqrt{b}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28867 (a b : ℝ) (hab : a = 6 ∧ b = 2) : √a - √b = √6 - √2   :=  by sorry
