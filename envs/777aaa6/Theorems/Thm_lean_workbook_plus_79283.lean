-- Prove2me | Theorems.Thm_lean_workbook_plus_79283
-- name    : lean_workbook_plus_79283
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/db39552d-e446-4b7e-add7-b241a85bef7c
-- statement:
--   A real number $x$ satisfies the equation $2014x + 1337 = 1337x + 2014$ . What is $x$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79283 (x : ℝ) (h : 2014*x + 1337 = 1337*x + 2014) : x = 1   :=  by sorry
