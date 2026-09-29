-- Prove2me | Theorems.Thm_lean_workbook_plus_55323
-- name    : lean_workbook_plus_55323
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/04b94795-83ad-4e71-a493-f1563ec01be2
-- statement:
--   Determine the validity of the statement 'If $a^5 - a^3 + a = 2$ and $a > 0$, then $a^3 \leq 2$.'
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55323 (a : ℝ) (h₁ : a > 0) (h₂ : a^5 - a^3 + a = 2) : a^3 ≤ 2   :=  by sorry
