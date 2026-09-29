-- Prove2me | Theorems.Thm_lean_workbook_plus_42570
-- name    : lean_workbook_plus_42570
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/58a3bc38-7588-4bc9-b0f7-93466fcbdc65
-- statement:
--   Prove that $(x-1)^{3}<x^{3}-x+3<x^{3}$ for $x > 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42570 (x : ℝ) (h : x > 3) : (x - 1) ^ 3 < x ^ 3 - x + 3 ∧ x ^ 3 - x + 3 < x ^ 3   :=  by sorry
