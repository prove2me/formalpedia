-- Prove2me | Theorems.Thm_lean_workbook_plus_57732
-- name    : lean_workbook_plus_57732
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d7725b42-9970-4af1-b4cb-a3ed6047e16f
-- statement:
--   Prove that when $x\in (0,1)$, $\sqrt{x}>x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57732 : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → Real.sqrt x > x   :=  by sorry
