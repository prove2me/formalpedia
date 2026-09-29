-- Prove2me | Theorems.Thm_lean_workbook_plus_7115
-- name    : lean_workbook_plus_7115
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b36988d5-fc0d-4b63-91ca-686aaaf365b8
-- statement:
--   Find the sum of $3 \times 4 \times 5 + 4 \times 5 \times 6 + 5 \times 6 \times 7 + ... + 99 \times 100 \times101$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7115 (n : ℕ) : ∑ k in Finset.Icc 3 99, (k * (k + 1) * (k + 2)) = 25497420   :=  by sorry
