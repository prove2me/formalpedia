-- Prove2me | Theorems.Thm_lean_workbook_plus_36363
-- name    : lean_workbook_plus_36363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/bb816700-90a1-42c9-b422-343e29bedf77
-- statement:
--   Let $ a,b,c$ be nonnegative real numbers such that $ ab + bc + ca = 3$ . Prove that \n\n $ (x^2a^2 + 1)(x^2b^2 + 1)(x^2c^2 + 1) =[x^3abc-x(a+b+c)]^2+[x^2(ab+bc+ca)-1]^2 \n\n $ \n\n $ \ge [x^2(ab+bc+ca)-1]^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36363 (a b c x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a * b + b * c + c * a = 3) : (x ^ 2 * a ^ 2 + 1) * (x ^ 2 * b ^ 2 + 1) * (x ^ 2 * c ^ 2 + 1) = (x ^ 3 * a * b * c - x * (a + b + c)) ^ 2 + (x ^ 2 * (a * b + b * c + c * a) - 1) ^ 2 ∧ (x ^ 2 * (a * b + b * c + c * a) - 1) ^ 2 ≤ (x ^ 2 * a ^ 2 + 1) * (x ^ 2 * b ^ 2 + 1) * (x ^ 2 * c ^ 2 + 1)   :=  by sorry
