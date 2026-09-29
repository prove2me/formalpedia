-- Prove2me | Theorems.Thm_lean_workbook_plus_18730
-- name    : lean_workbook_plus_18730
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/3b3ce01d-cc12-4093-9937-bfa882cbb140
-- statement:
--   Prove that $5k^4+500k>(k+1)^4+100k+100$ for natural numbers $k>4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18730 (k : ℕ) (h₁ : 4 < k) : 5 * k ^ 4 + 500 * k > (k + 1) ^ 4 + 100 * k + 100   :=  by sorry
