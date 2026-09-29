-- Prove2me | Theorems.Thm_lean_workbook_plus_41130
-- name    : lean_workbook_plus_41130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/55ab28aa-6483-42be-bb50-7729dfc5fcdc
-- statement:
--   Prove that $\sqrt{n(n+2)} < n+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41130 (n : ℕ) : Real.sqrt (n * (n + 2)) < n + 1   :=  by sorry
