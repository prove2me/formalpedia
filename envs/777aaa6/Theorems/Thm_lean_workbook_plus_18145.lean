-- Prove2me | Theorems.Thm_lean_workbook_plus_18145
-- name    : lean_workbook_plus_18145
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c1431d6c-223e-4f02-8675-cee36eef4562
-- statement:
--   Let $a,$ $b$ are different from zero real numbers. Prove that:\n $$\left(a^{2}+b^{2}\right)\left(\frac{1}{a^{2}}+\frac{1}{b^{2}}\right)+4\geq2\left(a+b\right)\left(\frac{1}{a}+\frac{1}{b}\right).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18145 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) : (a^2 + b^2) * (1 / a^2 + 1 / b^2) + 4 ≥ 2 * (a + b) * (1 / a + 1 / b)   :=  by sorry
