-- Prove2me | Theorems.Thm_lean_workbook_plus_53671
-- name    : lean_workbook_plus_53671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3b6bdf32-0d77-48d8-b05a-2593a7a82420
-- statement:
--   prove that: $A\ge B \Longrightarrow \ \ \ 2A\ge A+B$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53671 (A B : ℝ) (h : A ≥ B) : 2 * A ≥ A + B   :=  by sorry
