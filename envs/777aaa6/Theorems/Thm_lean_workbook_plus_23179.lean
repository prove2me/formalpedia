-- Prove2me | Theorems.Thm_lean_workbook_plus_23179
-- name    : lean_workbook_plus_23179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2d1069c1-a95e-42d7-b171-04f0ce101f20
-- statement:
--   Prove inequality, with $a$ and $b$ nonnegative real numbers: $\frac{a+b}{1+a+b}\leq \frac{a}{1+a} + \frac{b}{1+b} \leq \frac{2(a+b)}{2+a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23179 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) / (1 + a + b) ≤ a / (1 + a) + b / (1 + b) ∧ a / (1 + a) + b / (1 + b) ≤ (2 * (a + b)) / (2 + a + b)   :=  by sorry
