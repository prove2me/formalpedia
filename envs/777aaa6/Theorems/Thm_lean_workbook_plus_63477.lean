-- Prove2me | Theorems.Thm_lean_workbook_plus_63477
-- name    : lean_workbook_plus_63477
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/315c49bb-c6a2-4efa-8925-3d97e46da8ca
-- statement:
--   Solve the equation $a^b=1$ if $a=1$ and b is an integer or if $a\ne 0$ and b=0
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63477 (a b : ℂ) (h₁ : a = 1) (h₂ : b = 0) : a^b = 1   :=  by sorry
