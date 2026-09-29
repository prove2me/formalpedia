-- Prove2me | Theorems.Thm_lean_workbook_plus_43107
-- name    : lean_workbook_plus_43107
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6795176f-290c-416f-8a8e-7e2c0491718b
-- statement:
--   Given $1\le a, b\le3$ and $a+b=4$, prove that $|\sqrt{a}-\sqrt{b}| \le \sqrt{3}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43107 (a b : ℝ) (h₁ : 1 ≤ a ∧ a ≤ 3) (h₂ : 1 ≤ b ∧ b ≤ 3) (h₃ : a + b = 4) : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt 3 - 1   :=  by sorry
