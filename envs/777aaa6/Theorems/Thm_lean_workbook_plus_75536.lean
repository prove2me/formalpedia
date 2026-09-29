-- Prove2me | Theorems.Thm_lean_workbook_plus_75536
-- name    : lean_workbook_plus_75536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d9a9f8e9-c4e3-48de-904b-5f22239f4f93
-- statement:
--   Does the following inequality hold for all real numbers $\sqrt{1-u} \leq |1- \frac{1}{2}u|$ ???
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75536 (u : ℝ) : Real.sqrt (1 - u) ≤ |1 - 1 / 2 * u|   :=  by sorry
