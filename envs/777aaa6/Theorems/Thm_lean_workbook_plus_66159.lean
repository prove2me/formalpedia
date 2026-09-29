-- Prove2me | Theorems.Thm_lean_workbook_plus_66159
-- name    : lean_workbook_plus_66159
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e9e07c4d-2ab7-4edb-8839-47c63d4ba0bd
-- statement:
--   Prove that for any $r$, we have the algebraic identity:\n\n$(a^r + b^r - c^r)(a - b)^2 + (b^r + c^r - a^r)(b - c)^2 + (c^r + a^r - b^r)(c - a)^2 = 2[a^r(a - b)(a - c) + b^r(b - c)(b - a) + c^r (c - a)(c - b)]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66159 (a b c r : ℝ) : (a^r + b^r - c^r)*(a - b)^2 + (b^r + c^r - a^r)*(b - c)^2 + (c^r + a^r - b^r)*(c - a)^2 = 2*(a^r*(a - b)*(a - c) + b^r*(b - c)*(b - a) + c^r*(c - a)*(c - b))   :=  by sorry
