-- Prove2me | Theorems.Thm_lean_workbook_plus_28073
-- name    : lean_workbook_plus_28073
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/fb46c4be-33fe-48e4-aaa4-99c018ac9adb
-- statement:
--   $4+\sqrt{6}<k \leq 7+\sqrt{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28073 (k : ℝ) (h₁ : 4 + Real.sqrt 6 < k) (h₂ : k ≤ 7 + Real.sqrt 3) : 4 + Real.sqrt 6 < k ∧ k ≤ 7 + Real.sqrt 3   :=  by sorry
