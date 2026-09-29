-- Prove2me | Theorems.Thm_lean_workbook_plus_57727
-- name    : lean_workbook_plus_57727
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/87c9f62c-b4a3-4d2d-84be-08aa0731b8d6
-- statement:
--   We have $4\leq b+c+d+e\leq\frac{44}{5}$, but $a+b+c+d+e=8$, thus $4\geq a\geq-\frac{4}{5}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57727 (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8)  : -4 / 5 ≤ a ∧ a ≤ 4   :=  by sorry
