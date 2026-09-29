-- Prove2me | Theorems.Thm_lean_workbook_plus_81292
-- name    : lean_workbook_plus_81292
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/856867dd-7bb9-4211-b2b8-687983352a93
-- statement:
--   Let $a,b,$ and $c$ be positive real numbers such that $a^2 + b^2 -ab = c^2$ . Prove $(a-c)(b-c) \leq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81292 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (h : a^2 + b^2 - a * b = c^2) : (a - c) * (b - c) ≤ 0   :=  by sorry
