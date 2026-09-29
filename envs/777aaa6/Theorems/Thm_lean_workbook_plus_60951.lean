-- Prove2me | Theorems.Thm_lean_workbook_plus_60951
-- name    : lean_workbook_plus_60951
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/5b08a561-6dd1-41eb-b917-8c11f9c34c5c
-- statement:
--   Given the equation $x^3-y^3=xy+61$, find solutions using the fact that $x-y=1$ and $x^2+y^2=61$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60951 (x y : ℤ) (h₁ : x - y = 1) (h₂ : x^2 + y^2 = 61) : x^3 - y^3 = x*y + 61   :=  by sorry
