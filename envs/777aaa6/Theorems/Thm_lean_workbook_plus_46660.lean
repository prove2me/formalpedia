-- Prove2me | Theorems.Thm_lean_workbook_plus_46660
-- name    : lean_workbook_plus_46660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/80e37f73-0ccb-4560-af16-638fad4f5ad3
-- statement:
--   Solve for $ab$ given $a+b=1$ and $a^2+b^2=2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46660 (a b : ℝ) (h₁ : a + b = 1) (h₂ : a^2 + b^2 = 2) : a * b = -1 / 2   :=  by sorry
