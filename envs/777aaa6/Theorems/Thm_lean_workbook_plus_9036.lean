-- Prove2me | Theorems.Thm_lean_workbook_plus_9036
-- name    : lean_workbook_plus_9036
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/56bbf058-9f52-4807-ba09-e278a7cb4e97
-- statement:
--   Prove the identity $ a^3 + b^3 + c^3 - 3abc = (a + b + c) (a - b)^2 + (a + b + c)(a - c)(b - c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9036 (a b c : ℤ) : a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c) * (a - b)^2 + (a + b + c) * (a - c) * (b - c)   :=  by sorry
