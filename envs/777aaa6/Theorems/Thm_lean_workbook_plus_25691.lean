-- Prove2me | Theorems.Thm_lean_workbook_plus_25691
-- name    : lean_workbook_plus_25691
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6f6a8ce4-3c10-458d-96e7-bed07b55b6ab
-- statement:
--   A counting problem: Find the sum of ${5\choose1}+{5\choose3}+{5\choose5}$, which equals 16.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25691 : ∑ k in Finset.range 3, (Nat.choose 5 (2 * k + 1)) = 16   :=  by sorry
