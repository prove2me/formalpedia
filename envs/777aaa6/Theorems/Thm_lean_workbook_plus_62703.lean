-- Prove2me | Theorems.Thm_lean_workbook_plus_62703
-- name    : lean_workbook_plus_62703
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/d1aa3df3-4aec-4d69-94a4-c2e6689ee774
-- statement:
--   $ \sum_{r=0}^{n}{n\choose r}=2^n $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62703 (n : ℕ) : ∑ r in Finset.range (n+1), choose n r = 2^n   :=  by sorry
