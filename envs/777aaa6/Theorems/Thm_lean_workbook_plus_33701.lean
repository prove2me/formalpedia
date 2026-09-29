-- Prove2me | Theorems.Thm_lean_workbook_plus_33701
-- name    : lean_workbook_plus_33701
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/852d3931-6154-414c-a048-04a119e63d68
-- statement:
--   Find the sum of $3 \times 4 \times 5 + 4 \times 5 \times 6 + 5 \times 6 \times 7 + ... + 99 \times 100 \times101$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33701 (n : ℕ) : ∑ k in Finset.Icc 3 99, (k * (k + 1) * (k + 2)) = 333316500   :=  by sorry
