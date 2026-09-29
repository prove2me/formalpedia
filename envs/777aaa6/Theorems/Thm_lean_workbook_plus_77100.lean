-- Prove2me | Theorems.Thm_lean_workbook_plus_77100
-- name    : lean_workbook_plus_77100
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a7c425c1-28be-4ba7-8be8-93040e5d044e
-- statement:
--   Theorem. For $a,b,c\in C\wedge a+b+c=0$ we have $2(a^4+b^4+c^4)=(a^2+b^2+c^2)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77100 (a b c : ℂ) (h : a + b + c = 0) : 2 * (a^4 + b^4 + c^4) = (a^2 + b^2 + c^2)^2   :=  by sorry
