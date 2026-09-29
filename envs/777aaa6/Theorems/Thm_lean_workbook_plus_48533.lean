-- Prove2me | Theorems.Thm_lean_workbook_plus_48533
-- name    : lean_workbook_plus_48533
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/136e9400-f2e7-46c6-b787-c7c4414e0301
-- statement:
--   To prove that, if $ n$ is a natural number, then: $\sqrt {1} + .. + \sqrt {n}\leq n\sqrt {n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48533 : ∀ n : ℕ, ∑ i in Finset.range n, Real.sqrt i ≤ n * Real.sqrt n   :=  by sorry
