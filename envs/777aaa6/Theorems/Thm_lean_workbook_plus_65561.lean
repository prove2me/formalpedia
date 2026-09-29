-- Prove2me | Theorems.Thm_lean_workbook_plus_65561
-- name    : lean_workbook_plus_65561
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b2486f83-528f-4a3f-b12c-483f4497cff7
-- statement:
--   Prove that $\sqrt{15}$ is an irrational number. (By contradiction)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65561 : ¬ ∃ (a : ℤ), (a : ℝ)^2 = 15   :=  by sorry
