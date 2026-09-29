-- Prove2me | Theorems.Thm_lean_workbook_plus_62029
-- name    : lean_workbook_plus_62029
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/90fab07b-fbaf-4a36-a9c0-d3395e96f5fc
-- statement:
--   Find the value of the sum $\sum^{10}_{k=2}\binom{k}{2}\binom{12-k}{2}$ using the ogf derived earlier
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62029 (f : ℕ → ℕ) : ∑ k in Finset.Icc 2 10, (Nat.choose k 2 * Nat.choose (12 - k) 2) = 5148   :=  by sorry
