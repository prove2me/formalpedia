-- Prove2me | Theorems.Thm_lean_workbook_plus_4667
-- name    : lean_workbook_plus_4667
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5a9b1f95-0a90-4e86-b904-4acfe5d43a26
-- statement:
--   In a $\triangle ABC$ ,Prove that $sinBsinC+sinCsinA+sinAsinB\le \frac{\sqrt{3}}{2}(sinA+sinB+sinC).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4667 : ∀ (A B C : ℝ), (Real.sin B * Real.sin C + Real.sin C * Real.sin A + Real.sin A * Real.sin B) ≤ (Real.sqrt 3 / 2) * (Real.sin A + Real.sin B + Real.sin C)   :=  by sorry
