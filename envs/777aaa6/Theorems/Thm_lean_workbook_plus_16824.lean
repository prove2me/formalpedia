-- Prove2me | Theorems.Thm_lean_workbook_plus_16824
-- name    : lean_workbook_plus_16824
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d7da685e-a9d9-4d8a-a583-f952a216b36c
-- statement:
--   Prove the identity $a^3 + b^3 + c^3 - 3abc = (a+b+c)(a^2 + b^2 + c^2 - ab - ac - bc)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16824 (a b c : ℤ) : a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2 - a*b - a*c - b*c)   :=  by sorry
