-- Prove2me | Theorems.Thm_lean_workbook_plus_52971
-- name    : lean_workbook_plus_52971
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ca5aeb0c-9bbe-4851-8596-4fbeaa0495a3
-- statement:
--   Prove that for real numbers $a, b, c$ such that $a + b + c = 0$, the following inequality holds: $(a^2 + b^2 + c^2)^3 \geq 2(a - b)^2(b - c)^2(c - a)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52971 {a b c : ℝ} (h : a + b + c = 0) :
  (a^2 + b^2 + c^2)^3 ≥ 2 * (a - b)^2 * (b - c)^2 * (c - a)^2   :=  by sorry
