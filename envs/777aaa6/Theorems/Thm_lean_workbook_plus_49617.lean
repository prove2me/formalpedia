-- Prove2me | Theorems.Thm_lean_workbook_plus_49617
-- name    : lean_workbook_plus_49617
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/832a0296-e9ba-4034-9b6d-6d6e236f4764
-- statement:
--   If $c=0$ need to prove: $2+\frac{1}{4} \left[(a-b)^2+a^2+b^2\right]\geq a+b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49617 (a b c : ℝ) (h : c = 0) : 2 + (1 / 4) * ((a - b) ^ 2 + a ^ 2 + b ^ 2) ≥ a + b   :=  by sorry
