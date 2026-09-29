-- Prove2me | Theorems.Thm_lean_workbook_plus_52105
-- name    : lean_workbook_plus_52105
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/95aab99e-18b4-4ba7-9ef2-7196c772696f
-- statement:
--   Prove that $a^{2}+b^{2}+c^{2}+3\geq 2(a+b+c)$ when $abc=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52105 (a b c : ℝ) (h : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c)   :=  by sorry
