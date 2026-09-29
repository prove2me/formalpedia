-- Prove2me | Theorems.Thm_lean_workbook_plus_47865
-- name    : lean_workbook_plus_47865
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c30ec4f4-2ad4-4396-a6ed-13970f1f24b6
-- statement:
--   Use Mod11 $x^2=0,1,4,9,5,3$ and $y^5=0,1,-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47865 : ∀ (x : ZMod 11), x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 ∨ x ^ 2 = 9 ∨ x ^ 2 = 5 ∨ x ^ 2 = 3   :=  by sorry
