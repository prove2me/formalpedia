-- Prove2me | Theorems.Thm_lean_workbook_plus_43384
-- name    : lean_workbook_plus_43384
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/00fbd52b-7d5c-48ed-a31e-83d93e324acb
-- statement:
--   Prove that: $\frac{a}{1+bc}+\frac{b}{1+ac}+\frac{c}{1+ab}\leq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43384 : ∀ a b c : ℝ, (a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ≤ 2)   :=  by sorry
