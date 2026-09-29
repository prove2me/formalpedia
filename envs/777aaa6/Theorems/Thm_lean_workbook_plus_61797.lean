-- Prove2me | Theorems.Thm_lean_workbook_plus_61797
-- name    : lean_workbook_plus_61797
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8d636a61-25d2-47f7-ab59-9a2261be88ad
-- statement:
--   Then, $ f_0 = h_1 - h_2, h_1 = \max \{f_0,0\}, h_2 = - \min \{f_0,0\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61797 (f0 : ℝ) : ∃ h1 h2 : ℝ, h1 = max (f0) 0 ∧ h2 = -min (f0) 0   :=  by sorry
