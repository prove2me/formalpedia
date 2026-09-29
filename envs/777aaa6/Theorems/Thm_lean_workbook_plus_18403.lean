-- Prove2me | Theorems.Thm_lean_workbook_plus_18403
-- name    : lean_workbook_plus_18403
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9bf2f2d2-0941-4064-8594-7d6def892bea
-- statement:
--   $(r_1^2+r_2^2+\ldots+r_n^2)\left(\frac{1}{r_1^2}+\frac{1}{r_2^2}+\ldots+\frac{1}{r_n^2}\right) \geq\left(r_1\cdot\frac{1}{r_1}+r_2\cdot\frac{1}{r_2}+\ldots+r_n\cdot\frac{1}{r_n}\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18403 (n : ℕ) (r : ℕ → ℝ) : (∑ i in Finset.range n, (r i)^2) * (∑ i in Finset.range n, (1 / (r i))^2) ≥ (∑ i in Finset.range n, r i * (1 / r i))^2   :=  by sorry
