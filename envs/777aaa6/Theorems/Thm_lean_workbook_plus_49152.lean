-- Prove2me | Theorems.Thm_lean_workbook_plus_49152
-- name    : lean_workbook_plus_49152
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fdc3933b-60eb-41ee-abe4-5f8402ae0871
-- statement:
--   Evaluate: $\sum_{k=1}^{n}\frac{2^k}{k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49152 (n : ℕ) : ∑ k in Finset.Icc 1 n, (2 : ℝ)^k / k = ∑ k in Finset.Icc 1 n, (2 : ℝ)^k / k   :=  by sorry
