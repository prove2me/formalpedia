-- Prove2me | Theorems.Thm_lean_workbook_plus_51292
-- name    : lean_workbook_plus_51292
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/8c8a43e6-9e4a-4b4a-9344-1b308dde1955
-- statement:
--   Let $N=\prod_{k=1}^{1006}(2k-1).$ Prove that $N \equiv 3 \mod 8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51292 : (∏ k in Finset.Icc 1 1006, (2 * k - 1)) % 8 = 3   :=  by sorry
