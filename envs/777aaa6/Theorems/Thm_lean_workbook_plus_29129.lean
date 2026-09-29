-- Prove2me | Theorems.Thm_lean_workbook_plus_29129
-- name    : lean_workbook_plus_29129
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/baa94ace-1d07-448b-8994-7e87a38a04e7
-- statement:
--   If $a,b$ are non-negative reals, such that $a+b=2$ , prove that $a^{4}+b^{4}\ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29129 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 2) : a^4 + b^4 ≥ 2   :=  by sorry
