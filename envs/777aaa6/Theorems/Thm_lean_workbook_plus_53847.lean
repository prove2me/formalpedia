-- Prove2me | Theorems.Thm_lean_workbook_plus_53847
-- name    : lean_workbook_plus_53847
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5d12e4b9-85b0-4f66-8fd5-d96f3150645a
-- statement:
--   Prove that $(x-1)(y-1) \geq 1$ implies $xy \geq x+y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53847 (x y : ℝ) (h : (x - 1) * (y - 1) ≥ 1) : x * y ≥ x + y   :=  by sorry
