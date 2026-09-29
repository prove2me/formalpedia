-- Prove2me | Theorems.Thm_lean_workbook_plus_39418
-- name    : lean_workbook_plus_39418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8f9bdb88-36b0-4f3f-9db7-a74efab54488
-- statement:
--   Let $a,b$ be positive numbers satisfying $a+b=1$ . Prove that $\frac{8}{a}+\frac{27}{b^2}\geq 80.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39418 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : 8 / a + 27 / b ^ 2 ≥ 80   :=  by sorry
