-- Prove2me | Theorems.Thm_lean_workbook_plus_21682
-- name    : lean_workbook_plus_21682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/3f5dad4c-cbff-4d24-815b-833b94a860dc
-- statement:
--   If $a, b$ and $c$ are the lengths of the sides of a triangle, show that \n $$3(ab+bc+ca) \le (a+b+c)^2 \le 4(ab+bc+ca).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21682 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 ∧ (a + b + c) ^ 2 ≤ 4 * (a * b + b * c + c * a)   :=  by sorry
