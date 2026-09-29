-- Prove2me | Theorems.Thm_lean_workbook_plus_35689
-- name    : lean_workbook_plus_35689
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/16156aac-c915-4e53-a1ba-3cfe211a3f7f
-- statement:
--   $\sum_{k=1}^n ( 2k - 1 )^3=\sum_{k=1}^n ( 8k^3 - 12k^2 + 6k - 1 )$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35689 : ∀ n, ∑ k in Finset.Icc 1 n, ( 2 * k - 1 )^3 = ∑ k in Finset.Icc 1 n, ( 8 * k^3 - 12 * k^2 + 6 * k - 1 )   :=  by sorry
