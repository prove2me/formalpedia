-- Prove2me | Theorems.Thm_lean_workbook_plus_72931
-- name    : lean_workbook_plus_72931
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d6831ff5-9a60-42ad-8827-cedb45716e1e
-- statement:
--   $\Rightarrow \frac{1}{1+a}\geq \frac{2\sqrt{bc}}{\sqrt{(1+b)(1+c)}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72931 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 1 / (1 + a) ≥ 2 * Real.sqrt (b * c) / Real.sqrt ((1 + b) * (1 + c))   :=  by sorry
