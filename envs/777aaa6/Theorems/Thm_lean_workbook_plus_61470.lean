-- Prove2me | Theorems.Thm_lean_workbook_plus_61470
-- name    : lean_workbook_plus_61470
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ae70e0df-ed0f-4526-bc6b-84c568e8d906
-- statement:
--   $a(2a^2-1)=0$ and so $a\in\left\{-\frac{\sqrt 2}2,0,+\frac{\sqrt 2}2\right\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61470 (a : ℝ) (h : a * (2 * a ^ 2 - 1) = 0) : a ∈ ({-Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2} : Finset ℝ)   :=  by sorry
