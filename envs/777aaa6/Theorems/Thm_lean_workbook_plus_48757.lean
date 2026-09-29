-- Prove2me | Theorems.Thm_lean_workbook_plus_48757
-- name    : lean_workbook_plus_48757
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d6176681-59ca-498a-a628-65ba8cb14b93
-- statement:
--   Find the value of $1 + 2 + 3... + 2500 + 2501$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48757 : ∑ i in Finset.range 2502, i = 3131251   :=  by sorry
