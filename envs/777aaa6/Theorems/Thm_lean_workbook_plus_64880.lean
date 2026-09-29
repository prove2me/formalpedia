-- Prove2me | Theorems.Thm_lean_workbook_plus_64880
-- name    : lean_workbook_plus_64880
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/bf567ff4-7fb5-4515-a767-486a96d71020
-- statement:
--   Given $a$, $b$, and $c$ are positive numbers, prove that $a^{3}+b^{3}+c^{3}-3abc\geq 3|(a-b)(b-c)(c-a)|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64880 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 - 3*a*b*c ≥ 3 * |(a - b) * (b - c) * (c - a)|   :=  by sorry
