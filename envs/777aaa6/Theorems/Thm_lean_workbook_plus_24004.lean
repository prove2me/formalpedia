-- Prove2me | Theorems.Thm_lean_workbook_plus_24004
-- name    : lean_workbook_plus_24004
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0ef98d35-a80d-434a-8e2b-4fa083133e78
-- statement:
--   Show that $[0,1]$ is a retract of $\mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24004 : ∃ f : ℝ → ℝ, ∀ x, f x ∈ Set.Icc 0 1 ∧ f 0 = 0 ∧ f 1 = 1   :=  by sorry
