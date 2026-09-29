-- Prove2me | Theorems.Thm_lean_workbook_plus_59599
-- name    : lean_workbook_plus_59599
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/86dfc52e-ad3b-4f20-b54e-e6251db75c93
-- statement:
--   Let $\alpha = \frac{\sqrt{k+3}+\sqrt{k-1}}{2}$ and $\beta = \frac{\sqrt{k+3}-\sqrt{k-1}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59599 (α β : ℝ) (k : ℝ) : α = (Real.sqrt (k + 3) + Real.sqrt (k - 1)) / 2 ∧ β = (Real.sqrt (k + 3) - Real.sqrt (k - 1)) / 2 ↔ α + β = Real.sqrt (k + 3) ∧ α - β = Real.sqrt (k - 1)   :=  by sorry
