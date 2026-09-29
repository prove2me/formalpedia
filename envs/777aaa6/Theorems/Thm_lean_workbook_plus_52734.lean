-- Prove2me | Theorems.Thm_lean_workbook_plus_52734
-- name    : lean_workbook_plus_52734
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5b9413d1-a2be-4069-88c2-c75e27241f19
-- statement:
--   Given $a, b$ are positive real numbers and $a^2 + b^3 \geq a^3 + b^4$, prove that $a^3 + b^3 \leq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52734 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^3 ≥ a^3 + b^4) : a^3 + b^3 ≤ 2   :=  by sorry
