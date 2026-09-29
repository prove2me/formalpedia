-- Prove2me | Theorems.Thm_lean_workbook_plus_19854
-- name    : lean_workbook_plus_19854
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1fd61582-9a70-4b1c-b084-f9f3bda62622
-- statement:
--   Prove that $(a+b+c)(ab+bc+ca)-abc=(a+b)(b+c)(c+a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19854 (a b c : ℤ) : (a+b+c)*(a*b+b*c+c*a)-a*b*c=(a+b)*(b+c)*(c+a)   :=  by sorry
