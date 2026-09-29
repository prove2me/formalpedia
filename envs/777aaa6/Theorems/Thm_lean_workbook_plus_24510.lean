-- Prove2me | Theorems.Thm_lean_workbook_plus_24510
-- name    : lean_workbook_plus_24510
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/73fe6c7a-dac8-42f8-b8a5-65df387e763d
-- statement:
--   Derive the sum of the first n natural numbers: $\sum_{k=1}^nk=\frac{n(n+1)}2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24510 (n : ℕ) : ∑ k in Finset.range (n + 1), k = n * (n + 1) / 2   :=  by sorry
