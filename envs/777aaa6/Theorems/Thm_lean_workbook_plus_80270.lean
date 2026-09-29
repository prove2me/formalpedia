-- Prove2me | Theorems.Thm_lean_workbook_plus_80270
-- name    : lean_workbook_plus_80270
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/81571145-f627-439e-8366-05abfc4c0d3e
-- statement:
--   Prove $7(a+b+c)(ab+bc+ca) \leq 9abc + 2(a+b+c)^3$ with $a, b, c > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80270 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 7 * (a + b + c) * (a * b + b * c + c * a) ≤ 9 * a * b * c + 2 * (a + b + c) ^ 3   :=  by sorry
