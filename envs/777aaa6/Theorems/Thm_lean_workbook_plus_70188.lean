-- Prove2me | Theorems.Thm_lean_workbook_plus_70188
-- name    : lean_workbook_plus_70188
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/fd7d7625-f984-4fc6-981e-f502dfeafa6c
-- statement:
--   Equality for $a=b=c=\\frac{1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70188 (a b c : ℝ) (h : a = 1 / 3 ∧ b = 1 / 3 ∧ c = 1 / 3) :
  a * b + b * c + c * a = 1 / 3 * 1 / 3 + 1 / 3 * 1 / 3 + 1 / 3 * 1 / 3   :=  by sorry
