-- Prove2me | Theorems.Thm_lean_workbook_plus_17089
-- name    : lean_workbook_plus_17089
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d27651bd-a42b-4fdd-95e1-e0dd244a6a4d
-- statement:
--   Prove that $|ab|=|a||b|$ and $|b-a|=|a-b|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17089 (a b : ℝ) : |a * b| = |a| * |b| ∧  |b - a| = |a - b|   :=  by sorry
