-- Prove2me | Theorems.Thm_lean_workbook_plus_61757
-- name    : lean_workbook_plus_61757
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4c08e189-022b-4c66-8aa6-54b181129d98
-- statement:
--   For $x\in (-1,0)$ we have $e^x<1<\frac{1}{1+x}$ and for $x\in (0,\infty )$ we have $e^x>1>\frac{1}{1+x}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61757 : ∀ x ∈ Set.Ioo (-1 : ℝ) 0, exp x < 1 ∧ 1 < 1 / (1 + x) ∧ ∀ x ∈ Set.Ioi 0, exp x > 1 ∧ 1 > 1 / (1 + x)   :=  by sorry
