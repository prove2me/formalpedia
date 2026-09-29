-- Prove2me | Theorems.Thm_lean_workbook_plus_52001
-- name    : lean_workbook_plus_52001
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3fdec9a0-e7c7-4860-bbbb-34f9e9644fa3
-- statement:
--   Prove that $\sqrt{2}$ is irrational.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52001 : ¬ ∃ (x : ℚ), ↑x = Real.sqrt 2   :=  by sorry
