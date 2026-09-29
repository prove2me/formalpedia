-- Prove2me | Theorems.Thm_lean_workbook_plus_82434
-- name    : lean_workbook_plus_82434
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f634a76f-ee39-4150-b6f5-435095317433
-- statement:
--   Show that $3^{2x}-3^x+1 < 1$ for x < 0.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82434 (x : ℝ) (hx : x < 0) :
  (3:ℝ)^(2 * x) - (3:ℝ)^x + 1 < 1   :=  by sorry
