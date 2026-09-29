-- Prove2me | Theorems.Thm_lean_workbook_plus_21992
-- name    : lean_workbook_plus_21992
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/28d2353b-12df-4120-8d7e-eab4a37440f2
-- statement:
--   Prove that $([\sqrt{n}+1])^2 \ge n+1$ where $[x]$ is the integer part (floor function) of $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21992 : ∀ n : ℕ, (⌊Real.sqrt n + 1⌋ ^ 2) ≥ n + 1   :=  by sorry
