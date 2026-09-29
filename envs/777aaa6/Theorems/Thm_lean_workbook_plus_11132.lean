-- Prove2me | Theorems.Thm_lean_workbook_plus_11132
-- name    : lean_workbook_plus_11132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/dabea4c1-49af-420e-b4af-4143485693a3
-- statement:
--   prove that: for $k>1$, $\frac{1}{\sqrt{k}+\sqrt{k-1}}<\frac{1}{\sqrt{k}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11132 (k : ℕ) (h : 1 < k) : (1:ℝ) / (Real.sqrt k + Real.sqrt (k - 1)) < (1:ℝ) / Real.sqrt k   :=  by sorry
