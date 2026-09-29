-- Prove2me | Theorems.Thm_lean_workbook_plus_4449
-- name    : lean_workbook_plus_4449
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/2d018093-65e7-4252-a98a-3c0b3e95ce18
-- statement:
--   Evaluate $\binom{2}{2} + \binom{3}{2} + \binom{4}{2} + \ldots + \binom{42}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4449 (n : ℕ) : ∑ k in Finset.Icc 2 42, (Nat.choose k 2) = 1170   :=  by sorry
