-- Prove2me | Theorems.Thm_lean_workbook_plus_61495
-- name    : lean_workbook_plus_61495
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b3509683-eb82-4d89-ae3f-cc424be62d9c
-- statement:
--   Calculate the sum of the series: $\sum_{x=2}^{13}{479x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61495 (f : ℕ → ℕ) : ∑ x in Finset.Icc 2 13, 479 * x = 43110   :=  by sorry
