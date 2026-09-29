-- Prove2me | Theorems.Thm_lean_workbook_plus_66381
-- name    : lean_workbook_plus_66381
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5ce438c4-706d-42ce-b505-cdc171bd89b9
-- statement:
--   Given that $x+y=3, x^2+y^2-xy=4$ , find the value of $x^4+y^4+x^3y+xy^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66381 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36   :=  by sorry
