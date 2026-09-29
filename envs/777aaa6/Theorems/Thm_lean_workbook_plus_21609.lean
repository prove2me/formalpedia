-- Prove2me | Theorems.Thm_lean_workbook_plus_21609
-- name    : lean_workbook_plus_21609
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/17bd127d-3155-45ed-b0a0-430bdadb17c7
-- statement:
--   Let $ a$ and $ b$ are positive numbers such that $ a+b\leq1.$ Prove that: $ \left(1-\frac{1}{a}\right)\left(1-\frac{1}{b}\right)\geq\left(1-\frac{2}{a+b}\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21609 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) : (1 - 1 / a) * (1 - 1 / b) ≥ (1 - 2 / (a + b)) ^ 2   :=  by sorry
