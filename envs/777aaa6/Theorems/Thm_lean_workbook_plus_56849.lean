-- Prove2me | Theorems.Thm_lean_workbook_plus_56849
-- name    : lean_workbook_plus_56849
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/c007307d-6994-41f9-b11e-a6c44caa3fa7
-- statement:
--   Prove that, there exists infinite triples $(a,b,c)$ of integers such that $9a^3+4b^3-48c^3+36abc=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56849 : ∃ a b c : ℤ, 9*a^3 + 4*b^3 - 48*c^3 + 36*a*b*c = 1   :=  by sorry
