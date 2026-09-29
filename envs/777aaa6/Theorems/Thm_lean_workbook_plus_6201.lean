-- Prove2me | Theorems.Thm_lean_workbook_plus_6201
-- name    : lean_workbook_plus_6201
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/10617bc6-7f72-403a-a4fc-98ee1db8a495
-- statement:
--   Let $a,b$ be real numbers. Prove that $2(a^2+1)(b^2+1)\ge (a+1)(b+1)(ab+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6201 (a b : ℝ) : 2 * (a ^ 2 + 1) * (b ^ 2 + 1) ≥ (a + 1) * (b + 1) * (a * b + 1)   :=  by sorry
