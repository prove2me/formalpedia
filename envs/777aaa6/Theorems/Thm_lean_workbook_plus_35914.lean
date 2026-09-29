-- Prove2me | Theorems.Thm_lean_workbook_plus_35914
-- name    : lean_workbook_plus_35914
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/858f8f6f-d239-4806-981d-079641c20c1c
-- statement:
--   Solve for $x$ in the equation $x - 5\sqrt[3]{4} = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35914 (x : ℝ) : x - 5 * (4:ℝ)^(1/3) = 0 ↔ x = 5 * (4:ℝ)^(1/3)   :=  by sorry
