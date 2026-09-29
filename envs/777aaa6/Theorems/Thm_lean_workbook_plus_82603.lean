-- Prove2me | Theorems.Thm_lean_workbook_plus_82603
-- name    : lean_workbook_plus_82603
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/bdaa7de4-5553-458e-a227-b145e3156fce
-- statement:
--   We have \n$$\binom{2r+1}{0} + \binom{2r+1}{1} + \binom{2r+1}{2} + \cdots + \binom{2r+1}{2r+1} - \left(\binom{2r+1}{0} + \binom{2r+1}{2r+1}\right) = 2^{2r+1} - 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82603 (r : ℕ) : ∑ k in Finset.range (2 * r + 2), (Nat.choose (2 * r + 1) k) - 2 = 2^(2 * r + 1) - 2   :=  by sorry
