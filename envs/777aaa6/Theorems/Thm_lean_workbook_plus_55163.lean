-- Prove2me | Theorems.Thm_lean_workbook_plus_55163
-- name    : lean_workbook_plus_55163
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/035f7974-2879-4aa4-ab01-0f7d1d2970c2
-- statement:
--   Prove $4(1+abc)\ge (a+1)(b+1)(c+1)$ for all positive real numbers $a$ , $b$ , $c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55163 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 4*(1+a*b*c) ≥ (a+1)*(b+1)*(c+1)   :=  by sorry
