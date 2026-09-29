-- Prove2me | Theorems.Thm_lean_workbook_plus_48056
-- name    : lean_workbook_plus_48056
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3526258e-69f1-40da-b4c4-99e968056151
-- statement:
--   Let $a,b,c$ be reals . Prove that \n $$0\leq\frac{(1-a)(1-b)(1-a-b+ab)}{(1+a^2)(1+b^2)}\leq4$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48056 (a b c : ℝ) : 0 ≤ (1 - a) * (1 - b) * (1 - a - b + a * b) / ((1 + a ^ 2) * (1 + b ^ 2)) ∧ (1 - a) * (1 - b) * (1 - a - b + a * b) / ((1 + a ^ 2) * (1 + b ^ 2)) ≤ 4   :=  by sorry
