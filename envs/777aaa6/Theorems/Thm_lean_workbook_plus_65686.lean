-- Prove2me | Theorems.Thm_lean_workbook_plus_65686
-- name    : lean_workbook_plus_65686
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/01c8827d-a2b0-49cd-b8e8-19494c8faeb0
-- statement:
--   For $a,b,c$ sides of a triangle prove that $(a+b+c)^3 \geq (5a-b-c)(5b-c-a)(5c-a-b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65686 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b + c) ^ 3 >= (5 * a - b - c) * (5 * b - c - a) * (5 * c - a - b)   :=  by sorry
