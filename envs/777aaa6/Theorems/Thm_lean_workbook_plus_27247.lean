-- Prove2me | Theorems.Thm_lean_workbook_plus_27247
-- name    : lean_workbook_plus_27247
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7baa8351-f1f3-48e1-b65b-5f3f6128eaa4
-- statement:
--   Let $a+b+c=0$ . Prove $a^3+b^3+c^3=3abc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27247 (a b c : ℝ) (hab : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c   :=  by sorry
