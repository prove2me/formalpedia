-- Prove2me | Theorems.Thm_lean_workbook_plus_45241
-- name    : lean_workbook_plus_45241
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/33bd9228-0836-450b-b628-8cddc0140f1b
-- statement:
--   Given that $ [x] $ gives the greatest integer less than or equal to $ x $, does the statement $ x \ge [x] $ hold true?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45241 (x : ℝ) : x ≥ Int.floor x   :=  by sorry
