-- Prove2me | Theorems.Thm_lean_workbook_plus_76658
-- name    : lean_workbook_plus_76658
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1136b1a7-cb68-484c-b34d-95ccff141502
-- statement:
--   Prove that $(1-u)^{1/u}<e^{-1}$ for $0<u<1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76658 : ∀ u : ℝ, 0 < u ∧ u < 1 → (1 - u) ^ (1 / u) < exp (-1)   :=  by sorry
