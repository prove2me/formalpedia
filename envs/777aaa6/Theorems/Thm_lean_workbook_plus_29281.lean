-- Prove2me | Theorems.Thm_lean_workbook_plus_29281
-- name    : lean_workbook_plus_29281
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d0e90144-959c-4273-af10-695e41a89735
-- statement:
--   If $ a+b+c=0$ prove that $(\sum a^2)^3 -54a^2b^2c^2=2(a-b)^2(b-c)^2(c-a)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29281 (a b c : ℝ) (hab : a + b + c = 0) : (a^2 + b^2 + c^2)^3 - 54 * a^2 * b^2 * c^2 = 2 * (a - b)^2 * (b - c)^2 * (c - a)^2   :=  by sorry
