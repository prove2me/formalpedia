-- Prove2me | Theorems.Thm_lean_workbook_plus_48725
-- name    : lean_workbook_plus_48725
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6aea4e6e-bc84-4c9b-acfa-b45a08a9091d
-- statement:
--   Determine the largest value of x for which \\( |x^2-4x-39601|\ge|x^2+4x-39601| \\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48725 (x : ℝ) : |x^2 - 4*x - 39601| ≥ |x^2 + 4*x - 39601| → x ≤ 199  :=  by sorry
