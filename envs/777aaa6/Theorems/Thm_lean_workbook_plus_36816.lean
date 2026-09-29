-- Prove2me | Theorems.Thm_lean_workbook_plus_36816
-- name    : lean_workbook_plus_36816
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8a731a5d-6128-4e23-91ca-00abdce344c6
-- statement:
--   Let $f(x)=e^{-x}+x-1$. We want to show that $f(x)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36816 : ∀ x, (Real.exp (-x) + x - 1) ≥ 0   :=  by sorry
