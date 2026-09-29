-- Prove2me | Theorems.Thm_lean_workbook_plus_13953
-- name    : lean_workbook_plus_13953
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9427c2fe-9bae-49e8-a33f-e1118fe9d406
-- statement:
--   Prove that $0 \leq \ln(1+\alpha) \leq \alpha$ for all $\alpha \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13953 (α : ℝ) (hα : 0 ≤ α) : 0 ≤ Real.log (1 + α) ∧ Real.log (1 + α) ≤ α   :=  by sorry
