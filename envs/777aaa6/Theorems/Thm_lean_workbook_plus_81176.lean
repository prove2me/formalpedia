-- Prove2me | Theorems.Thm_lean_workbook_plus_81176
-- name    : lean_workbook_plus_81176
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/86f21903-32f4-4d85-bbe8-70b9e0de173a
-- statement:
--   Prove that the sequence defined by $a_{n+1}=3a_{n-1}+\sqrt{8(a_n^2+a_{n-1}^2)}$ with $a_0=1$ and $a_1=41$ is all integers for $n\ge0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81176 (n : ℕ) (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 41) (a_rec : ∀ n, a (n + 1) = 3 * a (n - 1) + Real.sqrt (8 * (a n ^ 2 + a (n - 1) ^ 2))) : ∀ n, a n = ⌊a n⌋   :=  by sorry
