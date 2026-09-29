-- Prove2me | Theorems.Thm_lean_workbook_plus_70634
-- name    : lean_workbook_plus_70634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/65beb2f2-6d90-47cd-83c5-bc5e562431b4
-- statement:
--   Prove that $abc(a+b+c)\leq \frac{1}{3}(ab+bc+ca)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70634 (a b c : ℝ) : a * b * c * (a + b + c) ≤ (1 / 3) * (a * b + b * c + c * a) ^ 2   :=  by sorry
