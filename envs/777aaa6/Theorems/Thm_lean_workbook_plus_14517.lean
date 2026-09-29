-- Prove2me | Theorems.Thm_lean_workbook_plus_14517
-- name    : lean_workbook_plus_14517
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c00b531a-1cd8-4929-ad91-c2d6b9dea5c0
-- statement:
--   If $x=x\cdot a$ where $a<1$ , then $x=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14517 : ∀ x a : ℝ, (x = x * a ∧ a < 1) → x = 0   :=  by sorry
