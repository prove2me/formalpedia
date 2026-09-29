-- Prove2me | Theorems.Thm_lean_workbook_plus_61729
-- name    : lean_workbook_plus_61729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/69307d31-e7be-45ec-8971-7cff46d9eb44
-- statement:
--   Let $a,$ $b$ are different from zero real numbers. Prove that:\n $$\left(a^{2}+b^{2}\right)\left(\frac{1}{a^{2}}+\frac{1}{b^{2}}\right)+4\geq2\left(a+b\right)\left(\frac{1}{a}+\frac{1}{b}\right).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61729 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a^2 + b^2) * (1 / a^2 + 1 / b^2) + 4 ≥ 2 * (a + b) * (1 / a + 1 / b)   :=  by sorry
