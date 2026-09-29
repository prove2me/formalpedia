-- Prove2me | Theorems.Thm_lean_workbook_plus_60853
-- name    : lean_workbook_plus_60853
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4e9961d4-6ad1-464c-91dc-dee9d2851950
-- statement:
--   Deduce $a=b=0$ from the previous statements
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60853 (a b : ℝ) (h₁ : a * b = 0) (h₂ : a + b = 0) : a = 0 ∧ b = 0   :=  by sorry
