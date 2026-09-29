-- Prove2me | Theorems.Thm_lean_workbook_plus_32247
-- name    : lean_workbook_plus_32247
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/1cd6f109-0f45-48c8-8afa-ebe48b7df139
-- statement:
--   Determine the range of $ x$ such that $ x^2 - 4x \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32247 (x : ℝ) : x^2 - 4*x >= 0 ↔ x ≤ 0 ∨ x ≥ 4   :=  by sorry
