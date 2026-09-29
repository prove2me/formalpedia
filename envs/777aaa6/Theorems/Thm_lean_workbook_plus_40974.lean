-- Prove2me | Theorems.Thm_lean_workbook_plus_40974
-- name    : lean_workbook_plus_40974
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/db2c034e-85b2-4fd6-ac88-eae4c2dac865
-- statement:
--   Prove that $\sum_{i=1}^{64}\frac{1}{i} < 6.4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40974 : ∑ i in Finset.Icc (1 : ℕ) 64, (1 : ℝ) / i < 6.4   :=  by sorry
