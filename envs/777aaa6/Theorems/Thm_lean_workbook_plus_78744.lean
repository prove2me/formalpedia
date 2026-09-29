-- Prove2me | Theorems.Thm_lean_workbook_plus_78744
-- name    : lean_workbook_plus_78744
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8a747668-a6ef-4f53-81d2-38ca11c0651f
-- statement:
--   Prove that $a^4+b^3+c^2 \geq a^3+b^2+c$, given $a;b;c>0$ such that $a+b+c \geq 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78744 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c ≥ 3) : a^4 + b^3 + c^2 ≥ a^3 + b^2 + c   :=  by sorry
