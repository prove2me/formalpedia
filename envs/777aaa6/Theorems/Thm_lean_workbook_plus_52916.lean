-- Prove2me | Theorems.Thm_lean_workbook_plus_52916
-- name    : lean_workbook_plus_52916
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9929e795-10b4-461b-bf11-8c7156a42396
-- statement:
--   If $a$ , $b$ and $c$ are positive real numbers, not all equal, prove that $6abc<a^2(b+c)+b^2(c+a)+c^2(a+b)<2\left(a^3+b^3+c^3\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52916 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a ≠ b) (hbc : b ≠ c) (hca : a ≠ c) : 6 * a * b * c < a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) ∧ a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) < 2 * (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
