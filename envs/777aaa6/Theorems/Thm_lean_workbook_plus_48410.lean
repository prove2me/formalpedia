-- Prove2me | Theorems.Thm_lean_workbook_plus_48410
-- name    : lean_workbook_plus_48410
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/89b55e08-44d6-45d7-80ad-6bfcb467b0c6
-- statement:
--   Prove that $\sum_{n=0}^{k}\left(\binom{k}{n}\cdot r^{n}\right)=\left(r+1\right)^{k}$ for all real numbers $r$ and nonnegative integers $k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48410 (r : ℝ) (k : ℕ) : ∑ n in Finset.range (k+1), (Nat.choose k n * r ^ n) = (r + 1) ^ k   :=  by sorry
