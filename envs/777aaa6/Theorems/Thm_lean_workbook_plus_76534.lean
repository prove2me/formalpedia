-- Prove2me | Theorems.Thm_lean_workbook_plus_76534
-- name    : lean_workbook_plus_76534
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/252b87ef-456c-454c-be98-67af41507065
-- statement:
--   Prove that $1/15 < 1/2*3/4*5/6*7/8*...*99/100 < 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76534 : 1 / 15 < ∏ i in Finset.Icc (1 : ℕ) 99, (i + 1) / (i + 2) ∧ ∏ i in Finset.Icc (1 : ℕ) 99, (i + 1) / (i + 2) < 1   :=  by sorry
