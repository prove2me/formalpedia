-- Prove2me | Theorems.Thm_lean_workbook_plus_58775
-- name    : lean_workbook_plus_58775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/423e2f72-c25f-4d35-953b-ce3da0a5bd00
-- statement:
--   Let $ a,b\geq0.$ Prove that $\frac{a+1}{b+1}+\frac{3a+b+1}{a+3b+1}+\frac{6a+b+1}{a+6b+1}\geq \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58775 (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : (a + 1) / (b + 1) + (3 * a + b + 1) / (a + 3 * b + 1) + (6 * a + b + 1) / (a + 6 * b + 1) ≥ 1 / 2   :=  by sorry
