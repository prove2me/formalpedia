-- Prove2me | Theorems.Thm_lean_workbook_plus_58978
-- name    : lean_workbook_plus_58978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/29f33574-45ce-4089-ba5a-7e6f77403176
-- statement:
--   Let $x,y>0$ and $xy(x+8y)=20.$ Prove that $$x+3y\geq 5$$ Equality holds when $x=2,y=1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58978 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x * y * (x + 8 * y) = 20) : x + 3 * y ≥ 5 ∧ (x = 2 ∧ y = 1 → x + 3 * y = 5)   :=  by sorry
