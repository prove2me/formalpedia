-- Prove2me | Theorems.Thm_lean_workbook_plus_57734
-- name    : lean_workbook_plus_57734
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d96d4a78-223c-4142-9861-4b5f830e6217
-- statement:
--   So we need to proof that $\sum_{i=0}^{n}{\frac{i}{2^i}} < 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57734 (n : ℕ) : ∑ i in Finset.range (n + 1), (i / 2 ^ i) < 2   :=  by sorry
