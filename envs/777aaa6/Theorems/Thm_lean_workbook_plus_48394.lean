-- Prove2me | Theorems.Thm_lean_workbook_plus_48394
-- name    : lean_workbook_plus_48394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b425b17a-a7bf-4499-8675-4af714581b8c
-- statement:
--   substitution $ a=x+y,b=y+z,c=z+x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48394 (x y z a b c : ℝ) (h₁ : a = x + y) (h₂ : b = y + z) (h₃ : c = z + x) : a + b + c = x + y + (y + z) + (z + x)   :=  by sorry
