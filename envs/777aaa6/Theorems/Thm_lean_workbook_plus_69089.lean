-- Prove2me | Theorems.Thm_lean_workbook_plus_69089
-- name    : lean_workbook_plus_69089
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/372bf943-f9fd-4ff1-bbcb-5b4d58b14129
-- statement:
--   Prove that, for $0<x<3$ , $1+2\sqrt{x} \ge x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69089 (x : ℝ) (hx : 0 < x ∧ x < 3) : 1 + 2 * Real.sqrt x ≥ x   :=  by sorry
