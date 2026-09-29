-- Prove2me | Theorems.Thm_lean_workbook_plus_19339
-- name    : lean_workbook_plus_19339
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d12811ff-1e3d-434f-93fa-29cd3643bef7
-- statement:
--   Prove that for all positive integers \( n \), \(\prod_{r=1}^{n} \frac{2r-1}{2r} <\frac{1}{\sqrt {3n+1}}\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19339 : ∀ n : ℕ, ∏ r in Finset.Icc 1 n, ((2 * r - 1) / (2 * r)) < 1 / (Real.sqrt (3 * n + 1))   :=  by sorry
