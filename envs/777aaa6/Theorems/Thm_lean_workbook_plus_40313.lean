-- Prove2me | Theorems.Thm_lean_workbook_plus_40313
-- name    : lean_workbook_plus_40313
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3372e036-6212-4859-989a-5cd13b2a1ce3
-- statement:
--   prove that if $ab=0$ , either $a$ or $b$ must be $0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40313 (a b : ℝ) (h : a * b = 0) : a = 0 ∨ b = 0   :=  by sorry
