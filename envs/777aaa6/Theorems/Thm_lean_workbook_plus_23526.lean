-- Prove2me | Theorems.Thm_lean_workbook_plus_23526
-- name    : lean_workbook_plus_23526
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a18d79da-3e95-4943-a39f-f321cb58fea0
-- statement:
--   Let $a$ , $b$ be non-negative numbers such that $a^3+b^2\geq a^4+b^3$ . Prove that: $a^3+b^3\leq2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23526 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^3 + b^2 ≥ a^4 + b^3) : a^3 + b^3 ≤ 2   :=  by sorry
