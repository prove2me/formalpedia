-- Prove2me | Theorems.Thm_lean_workbook_plus_70079
-- name    : lean_workbook_plus_70079
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ff9f58bd-fac6-444a-bc7a-1eee55f295d0
-- statement:
--   Solution $ n-3 \in \{ -15,-5,-3,-1,1,3,5,15 \} \Rightarrow n \in \{ -12,-2,0,2,4,6,8,18 \}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70079 (n : ℤ) : n - 3 ∈ ({-15, -5, -3, -1, 1, 3, 5, 15} : Finset ℤ) ↔ n ∈ ({-12, -2, 0, 2, 4, 6, 8, 18} : Finset ℤ)   :=  by sorry
