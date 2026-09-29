-- Prove2me | Theorems.Thm_lean_workbook_plus_24586
-- name    : lean_workbook_plus_24586
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/240cfa7e-5db8-40bb-b809-0fad15ce090f
-- statement:
--   Let a,b,c be positive reals such that $a+b+c\leq3$ . Prove that $\frac{1}{1+a}+\frac{1}{1+b}+\frac{1}{1+c}\geq3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24586 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c ≤ 3) : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≥ 3   :=  by sorry
