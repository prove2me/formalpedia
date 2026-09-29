-- Prove2me | Theorems.Thm_lean_workbook_plus_28782
-- name    : lean_workbook_plus_28782
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/847eb09e-0295-43dc-a5d1-76e8fdda34c0
-- statement:
--   another inequality with the same condition Prove $(a+b-c)(b+c-a)(c+a-b)abc\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28782 (a b c : ℝ) (h : a + b > c ∧ a + c > b ∧ b + c > a) :
  (a + b - c) * (b + c - a) * (c + a - b) * a * b * c ≥ 0   :=  by sorry
