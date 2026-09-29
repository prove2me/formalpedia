-- Prove2me | Theorems.Thm_lean_workbook_plus_28156
-- name    : lean_workbook_plus_28156
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7395e473-88b0-47f8-9c37-a5893f0d8ce3
-- statement:
--   Prove that $a_n < b_n < c_n$ where $a_n= \frac{2}{3} \cdot \frac{5}{6} \cdot ... \cdot \frac{3n-1}{3n}$, $b_n= \frac{3}{4} \cdot \frac{6}{7} \cdot ... \cdot \frac{3n}{3n+1}$, and $c_n= \frac{4}{5} \cdot \frac{7}{8} \cdot ... \cdot \frac{3n+1}{3n+2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28156 : ∀ n : ℕ, (∏ i in Finset.range n, ((3 * i + 2) / (3 * i + 3))) < (∏ i in Finset.range n, ((3 * i + 3) / (3 * i + 4))) ∧ (∏ i in Finset.range n, ((3 * i + 3) / (3 * i + 4))) < (∏ i in Finset.range n, ((3 * i + 4) / (3 * i + 5)))   :=  by sorry
