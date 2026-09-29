-- Prove2me | Theorems.Thm_lean_workbook_plus_25427
-- name    : lean_workbook_plus_25427
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/142b7f91-1db0-4b5c-92a6-346231da2497
-- statement:
--   $ (x + 6)^2 = 0\Longrightarrow\fbox{x = - 6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25427  (x : ℝ)
  (h₀ : (x + 6)^2 = 0) :
  x = -6   :=  by sorry
