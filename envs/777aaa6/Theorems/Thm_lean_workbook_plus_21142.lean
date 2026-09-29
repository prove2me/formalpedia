-- Prove2me | Theorems.Thm_lean_workbook_plus_21142
-- name    : lean_workbook_plus_21142
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f814ff41-08b9-45f7-a7d9-8bd1743c79d4
-- statement:
--   Let $a,b$ be positive real numbers . Prove that $\frac{1}{1+a}-\frac{1}{1+b}+\frac{a}{a+b}< 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21142 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (1 + a) - 1 / (1 + b) + a / (a + b) < 1   :=  by sorry
