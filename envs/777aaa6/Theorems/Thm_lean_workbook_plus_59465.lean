-- Prove2me | Theorems.Thm_lean_workbook_plus_59465
-- name    : lean_workbook_plus_59465
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f78d0db7-064d-4d51-bc40-cb4b621f5cc9
-- statement:
--   Prove: $\sum_{i=0}^{m} \sum_{j=0}^{n} (-1)^{i+j} C_{m}^{i} C_{n}^{j} C_{i+j}^{i}=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59465 : ∀ m n : ℕ, (∑ i in Finset.range (m + 1), ∑ j in Finset.range (n + 1), (-1 : ℤ)^(i + j) * choose m i * choose n j * choose (i + j) i) = 0   :=  by sorry
