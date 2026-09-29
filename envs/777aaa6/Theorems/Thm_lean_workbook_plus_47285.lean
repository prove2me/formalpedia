-- Prove2me | Theorems.Thm_lean_workbook_plus_47285
-- name    : lean_workbook_plus_47285
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e253ba55-f45e-496a-ba72-43061ca7f7b6
-- statement:
--   If $ a,b,c$ are sides of a triangle, then \n\n $ a^3 + b^3 + c^3 - 3abc-2(c-b)^3$ \n\n $ =\frac{(a+9b-c)(c-a)^2+3(a+b-c)(c+a-2b)^2}{4}\geq0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47285 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + c^3 - 3 * a * b * c - 2 * (c - b)^3 ≥ 0   :=  by sorry
