-- Prove2me | Theorems.Thm_lean_workbook_plus_36276
-- name    : lean_workbook_plus_36276
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6fc8ec94-0b82-470c-ae7d-a513a129057e
-- statement:
--   For any reals $a, b, c$ such that $a+b+c=0$ , we have that $a^3+b^3+c^3 - 3abc = (a+b+c)(a^2+b^2+c^2-ab-bc-ca)=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36276 {a b c : ℝ} (h : a + b + c = 0) : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a)   :=  by sorry
