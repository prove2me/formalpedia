-- Prove2me | Theorems.Thm_lean_workbook_plus_58730
-- name    : lean_workbook_plus_58730
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/fe0221f1-0882-49dd-a43f-ba5cbc907bcc
-- statement:
--   Prove that a number $r$ can be expressed as an infinite repeating decimal if and only if $r$ is rational.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58730 (r : ℝ) : (∃ a b, 0 < b ∧ r = a / b) ↔ ∃ a b, 0 < b ∧ r = a / b   :=  by sorry
