-- Prove2me | Theorems.Thm_lean_workbook_plus_56569
-- name    : lean_workbook_plus_56569
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/1e8b1331-2c7c-4a4a-8e40-4610cfbecd85
-- statement:
--   Prove that $81abc(a+b+c)(a^2+b^2+c^2) \leq 27(ab+bc+ca)^2(a^2+b^2+c^2)$ given $a,b,c>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56569 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 81 * a * b * c * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 27 * (a * b + b * c + c * a) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
