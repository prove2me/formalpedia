-- Prove2me | Theorems.Thm_lean_workbook_plus_53946
-- name    : lean_workbook_plus_53946
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d5b839e8-61cf-4f1d-82a9-4d3a9033d54f
-- statement:
--   Let $a$ and $ b$ be real numbers with $0\le a, b\le 1$ . Prove that $$\frac{a}{b + 1}+\frac{b}{a + 1}\le 1$$ When does equality holds?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53946 (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : a / (b + 1) + b / (a + 1) ≤ 1   :=  by sorry
