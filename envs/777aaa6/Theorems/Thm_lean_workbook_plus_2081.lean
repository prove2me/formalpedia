-- Prove2me | Theorems.Thm_lean_workbook_plus_2081
-- name    : lean_workbook_plus_2081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a30a4a61-e3e3-41aa-886a-d2f8de1e47db
-- statement:
--   Which is $t(t-1)(t+2)(19t-30)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2081 (t : ℝ) : t * (t - 1) * (t + 2) * (19 * t - 30) = 0 ↔ t = 0 ∨ t = 1 ∨ t = -2 ∨ t = 30 / 19   :=  by sorry
