-- Prove2me | Theorems.Thm_lean_workbook_plus_42282
-- name    : lean_workbook_plus_42282
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d726cb1b-a4e9-42a6-bbb1-9bb4b779dfab
-- statement:
--   Prove that $1+\frac{1}{3^2}+\frac{1}{5^2}+\cdot \cdot \cdot +\frac{1}{(2n+1)^2} < \frac{5}{4}, \forall n \in \mathbb N .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42282 (n : ℕ) :
  ∑ k in Finset.range (n + 1), (1 / (2 * k + 1) ^ 2) < 5 / 4   :=  by sorry
