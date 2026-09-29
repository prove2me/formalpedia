-- Prove2me | Theorems.Thm_lean_workbook_plus_17632
-- name    : lean_workbook_plus_17632
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/59e655c0-8ba7-4e40-a81b-24c79a4813d9
-- statement:
--   Prove that if $c\neq 0$, then $3c=-2b-a$ and $c=a-2b$ imply $c=-b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17632 (a b c : ℝ) (h₁ : c ≠ 0) (h₂ : 3 * c = -2 * b - a) (h₃ : c = a - 2 * b) : c = -b   :=  by sorry
