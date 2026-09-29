-- Prove2me | Theorems.Thm_lean_workbook_plus_32360
-- name    : lean_workbook_plus_32360
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/8a2e7956-30c6-4544-bc57-2cdd8fb938bc
-- statement:
--   Derive the equation $x+z = p+q-r$ from $x+y+z = p +2q$ and $y = q+r$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32360 (x y z p q r : ℝ) (h₁ : x + y + z = p + 2*q) (h₂ : y = q + r) : x + z = p + q - r   :=  by sorry
