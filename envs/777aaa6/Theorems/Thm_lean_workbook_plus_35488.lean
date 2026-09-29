-- Prove2me | Theorems.Thm_lean_workbook_plus_35488
-- name    : lean_workbook_plus_35488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/42a747b4-9cf9-498c-b26d-def0d593f725
-- statement:
--   Solve the quadratic equation $a^2 - 34a + 240 = 0$ for $a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35488 (a : ℝ) (h : a^2 - 34*a + 240 = 0) : a = 10 ∨ a = 24   :=  by sorry
