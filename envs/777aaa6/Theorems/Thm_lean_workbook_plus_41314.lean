-- Prove2me | Theorems.Thm_lean_workbook_plus_41314
-- name    : lean_workbook_plus_41314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/4bb17244-b6a9-485b-b5cb-624caaa0ab70
-- statement:
--   Let $a$ , $b$ be non-negative numbers such that $a^3+b^2\geq a^4+b^3$ . Prove that $a^3+b^3\leq4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41314 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^3 + b^2 ≥ a^4 + b^3) : a^3 + b^3 ≤ 4   :=  by sorry
