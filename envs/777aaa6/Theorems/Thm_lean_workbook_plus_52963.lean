-- Prove2me | Theorems.Thm_lean_workbook_plus_52963
-- name    : lean_workbook_plus_52963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/52fd44f8-422b-499d-ad75-c3e89fdb0dc7
-- statement:
--   Let $a, b$ be the positive real numbers such that $\frac{1}{a}+\frac{a}{b}=4 .$ Prove that $$ a+\frac{b}{a}\geq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52963 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1/a + a/b = 4) : a + b/a ≥ 1   :=  by sorry
