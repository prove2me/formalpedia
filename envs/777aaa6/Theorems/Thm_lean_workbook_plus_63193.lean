-- Prove2me | Theorems.Thm_lean_workbook_plus_63193
-- name    : lean_workbook_plus_63193
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e15ffc82-d667-4520-bec1-7bc3386ee346
-- statement:
--   Given $b + c \geq 1 + bc$, prove that $2(b + c) \geq (b + 1)(c + 1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63193 (b c : ℝ) (h : b + c ≥ 1 + b * c) :
  2 * (b + c) ≥ (b + 1) * (c + 1)   :=  by sorry
