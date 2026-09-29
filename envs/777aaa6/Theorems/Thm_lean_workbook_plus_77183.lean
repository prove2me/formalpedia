-- Prove2me | Theorems.Thm_lean_workbook_plus_77183
-- name    : lean_workbook_plus_77183
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8b23b865-81ab-416a-9191-3b96d9659ca5
-- statement:
--   So $a^2=4 \mbox{ and then } a=\pm2$ ??
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77183  (a : ℝ)
  (h₀ : a^2 = 4) :
  a = 2 ∨ a = -2   :=  by sorry
