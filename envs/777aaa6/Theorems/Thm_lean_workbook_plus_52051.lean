-- Prove2me | Theorems.Thm_lean_workbook_plus_52051
-- name    : lean_workbook_plus_52051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/2035405b-7deb-410f-ac49-524187ecbe7f
-- statement:
--   Prove that any function $ g$ can be written in the form $ g=h+k$ where $ h$ is an even function and $ k$ is an odd function.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52051 (g : ℝ → ℝ) : ∃ h k : ℝ → ℝ, Even h ∧ Odd k ∧ g = h + k   :=  by sorry
