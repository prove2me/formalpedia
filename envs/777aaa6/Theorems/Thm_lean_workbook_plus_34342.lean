-- Prove2me | Theorems.Thm_lean_workbook_plus_34342
-- name    : lean_workbook_plus_34342
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/93258ac0-e8cc-4a61-bf0d-79177fa59229
-- statement:
--   Find the non-negative values of $b$ that satisfy the equation $b(b+1)=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34342 (b : ℝ) (h : b * (b + 1) = 0) : b = 0 ∨ b = -1   :=  by sorry
