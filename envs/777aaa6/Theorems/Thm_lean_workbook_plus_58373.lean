-- Prove2me | Theorems.Thm_lean_workbook_plus_58373
-- name    : lean_workbook_plus_58373
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/38c32cc0-244c-457d-8789-1b09508f0501
-- statement:
--   Prove that $1/2+1/2^2+....+1/2^n<1$ for $n \in \mathbb{Z^{+}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58373 (n : ℕ) : (∑ i in Finset.range n, (1 / (2^(i + 1)))) < 1   :=  by sorry
