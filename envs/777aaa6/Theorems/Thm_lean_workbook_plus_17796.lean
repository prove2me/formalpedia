-- Prove2me | Theorems.Thm_lean_workbook_plus_17796
-- name    : lean_workbook_plus_17796
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/02ab8315-7111-46e6-91c8-7ea8dff6c077
-- statement:
--   $\left(a+1\right)\left(a^3-4\right)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17796 (a : ℝ) (h : (a + 1) * (a ^ 3 - 4) = 0) : a = -1 ∨ a ^ 3 = 4   :=  by sorry
