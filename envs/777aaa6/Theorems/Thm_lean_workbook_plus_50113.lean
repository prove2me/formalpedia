-- Prove2me | Theorems.Thm_lean_workbook_plus_50113
-- name    : lean_workbook_plus_50113
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/07562482-b932-4ee8-9286-23326026a867
-- statement:
--   prove that $x+\frac2{x}\leq 3$ given $x\in[1,2]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50113 (x : ℝ) (h : 1 ≤ x ∧ x ≤ 2) : x + 2 / x ≤ 3   :=  by sorry
