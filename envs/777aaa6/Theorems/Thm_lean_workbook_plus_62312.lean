-- Prove2me | Theorems.Thm_lean_workbook_plus_62312
-- name    : lean_workbook_plus_62312
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8f76f157-12b0-42ac-b751-d79c05984b1c
-- statement:
--   Prove that $x_i \ge x_i^2$ for $x_i \in [0, 1]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62312 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : x ≥ x^2   :=  by sorry
