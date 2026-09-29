-- Prove2me | Theorems.Thm_lean_workbook_plus_193
-- name    : lean_workbook_plus_193
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8d78de8e-ca4e-4eca-9587-a15ceee2faef
-- statement:
--   Consider $(a^3+b^3+c^3) - (a+b+c) = a(a-1)(a+1) + b(b-1)(b+1) + c(c-1)(c+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_193 : ∀ a b c : ℤ, (a^3 + b^3 + c^3) - (a + b + c) = a*(a - 1)*(a + 1) + b*(b - 1)*(b + 1) + c*(c - 1)*(c + 1)   :=  by sorry
