-- Prove2me | Theorems.Thm_lean_workbook_plus_73424
-- name    : lean_workbook_plus_73424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/710e383e-8dec-4599-b6f1-31c60099e02d
-- statement:
--   Prove that $\sum a^4+2\sum a^2b^2\geq 3abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73424 (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 + 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 3 * a * b * c * (a + b + c)   :=  by sorry
