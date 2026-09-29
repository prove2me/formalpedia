-- Prove2me | Theorems.Thm_lean_workbook_plus_65237
-- name    : lean_workbook_plus_65237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/a3040e6b-c3c9-4509-b288-02a72744655c
-- statement:
--   Rearrange the first equation as $6y + 2x = xy$ Moving everything to the RHS and flipping, we have that $xy - 6y - 2x = 0$ Applying SFFT, we can add $12$ to both sides and factor the LHS to obtain $(x-6)(y-2)=12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65237  (x y : ℤ)
  (h₀ : 6 * y + 2 * x = x * y) :
  (x - 6) * (y - 2) = 12   :=  by sorry
