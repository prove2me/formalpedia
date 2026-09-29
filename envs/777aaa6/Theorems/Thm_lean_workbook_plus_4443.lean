-- Prove2me | Theorems.Thm_lean_workbook_plus_4443
-- name    : lean_workbook_plus_4443
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/39381006-724f-4fb5-b128-ac59bc044501
-- statement:
--   $\frac{1}{2} \sum a_1 \leq \frac{1}{6}\sum (a_1^3+1+1) = \frac{1}{6}\sum a_1^3 + \frac{n}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4443 (n : ℕ) (a : ℕ → ℕ) : 1/2 * ∑ i in Finset.range n, a i ≤ 1/6 * ∑ i in Finset.range n, (a i ^ 3 + 1 + 1)   :=  by sorry
