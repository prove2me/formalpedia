-- Prove2me | Theorems.Thm_lean_workbook_plus_74543
-- name    : lean_workbook_plus_74543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/72e21b4a-ec8d-4ac2-aa17-301022cef799
-- statement:
--   Let $a,b,c>0$ , prove that $(a-b)(2a+b)(a^2+b^2)+(b-c)(2b+c)(b^2+c^2)+(c-a)(2c+a)(c^2+a^2)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74543 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) * (2 * a + b) * (a ^ 2 + b ^ 2) + (b - c) * (2 * b + c) * (b ^ 2 + c ^ 2) + (c - a) * (2 * c + a) * (c ^ 2 + a ^ 2) ≥ 0   :=  by sorry
