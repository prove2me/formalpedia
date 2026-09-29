-- Prove2me | Theorems.Thm_lean_workbook_plus_2230
-- name    : lean_workbook_plus_2230
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/6642f73c-ac1e-401d-97dc-6f6793c5553d
-- statement:
--   $(a+b)^4+(b+c)^4+(c+a)^4\ge 8(a^3(b+c)+b^3(c+a)+c^3(a+b))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2230 (a b c : ℝ) : (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥ 8 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b))   :=  by sorry
