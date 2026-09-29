-- Prove2me | Theorems.Thm_lean_workbook_plus_18372
-- name    : lean_workbook_plus_18372
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/2c65602a-d447-4ebb-a5cd-f701a4702727
-- statement:
--   Prove that \(a^{2}+b^{2}+c^{2} \geq ab+bc+ca\) given \(a+b+c=1/a+1/b+1/c\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18372 (a b c : ℝ) (h : a + b + c = 1 / a + 1 / b + 1 / c) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a   :=  by sorry
