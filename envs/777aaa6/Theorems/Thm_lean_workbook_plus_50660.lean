-- Prove2me | Theorems.Thm_lean_workbook_plus_50660
-- name    : lean_workbook_plus_50660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5bb7efb0-9be7-43a1-83fb-618227d3c13f
-- statement:
--   Determine all possible ordered pairs $(a,b)$ such that $a-b = 1$ and $2a^2 + ab - 3b^2 = 22$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50660 (a b : ℝ) (h₁ : a - b = 1) (h₂ : 2*a^2 + a*b - 3*b^2 = 22) : a = 5 ∧ b = 4   :=  by sorry
