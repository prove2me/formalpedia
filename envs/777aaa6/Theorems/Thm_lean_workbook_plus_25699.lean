-- Prove2me | Theorems.Thm_lean_workbook_plus_25699
-- name    : lean_workbook_plus_25699
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/80ea94eb-3fa0-4f0c-b033-6659cde81cc8
-- statement:
--   prove that: \n\n $\left( a+b \right) \left( b+c \right) \left( c+d \right) \left( d+ a \right) \geq \left( a+b+c+d \right) \left( acd+abd+abc+bcd \right) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25699 (a b c d : ℝ) : (a + b) * (b + c) * (c + d) * (d + a) ≥ (a + b + c + d) * (a * c * d + a * b * d + a * b * c + b * c * d)   :=  by sorry
