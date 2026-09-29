-- Prove2me | Theorems.Thm_lean_workbook_plus_1237
-- name    : lean_workbook_plus_1237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a63c018b-060c-4f0d-8e6c-d36e706aa76a
-- statement:
--   Let $a, b$ be positive real numbers such that $a+b\le1$ . Prove that $\dfrac{1}{a}+\dfrac{1}{b}+a^2+b^2+3a+3b\ge\dfrac{15}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1237 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) : 1 / a + 1 / b + a ^ 2 + b ^ 2 + 3 * a + 3 * b ≥ 15 / 2   :=  by sorry
