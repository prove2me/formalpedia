-- Prove2me | Theorems.Thm_lean_workbook_plus_3497
-- name    : lean_workbook_plus_3497
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1221fec3-dbe9-4047-94b1-d4f8d72eee9c
-- statement:
--   $\frac{2}{n+1}\times \frac{4}{n+1}\times \ldots \times \frac{2n}{n+1}\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3497 (n : ℕ) : (∏ k in Finset.Icc 1 n, (2 * k) / (n + 1)) ≤ 1   :=  by sorry
