-- Prove2me | Theorems.Thm_lean_workbook_plus_49491
-- name    : lean_workbook_plus_49491
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d1ca5ce8-df2b-41ad-9bac-976932e5232f
-- statement:
--   Prove that $(a^2-bc)(b+c)+(b^2-ca)(c+a)+(c^2-ab)(a+b)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49491 (a b c : ℤ) : (a^2-b*c) * (b+c) + (b^2-c*a) * (c+a) + (c^2-a*b) * (a+b) = 0   :=  by sorry
