-- Prove2me | Theorems.Thm_lean_workbook_plus_27100
-- name    : lean_workbook_plus_27100
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/83bfcaa8-c184-48f8-9ad3-e3f5dfa334a4
-- statement:
--   Express $x$ and $y$ in terms of $a$ and $b$ where $a, b$ are positive: $x = a + 1$, $y = b + 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27100 (a b x y : ℝ) : x = a + 1 ∧ y = b + 1 ↔ a = x - 1 ∧ b = y - 1   :=  by sorry
