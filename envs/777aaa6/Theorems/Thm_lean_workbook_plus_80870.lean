-- Prove2me | Theorems.Thm_lean_workbook_plus_80870
-- name    : lean_workbook_plus_80870
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/58171935-84e7-47dd-9be4-35ef4b67aada
-- statement:
--   Prove that the sequence defined recursively by $a_1=0,a_2=1$ and $a_{4n} = 1 -a_{n+1}$, $a_{4n+2}=a_{n+2}$, $a_{2n+1} = a_n$ is not periodic.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80870 (a : ℕ → ℤ) (a1 : a 0 = 0) (a2 : a 1 = 1) (a_rec : ∀ n, a (4 * n) = 1 - a (n + 1) ∧ a (4 * n + 2) = a (n + 2) ∧ a (2 * n + 1) = a n) : ¬ ∃ n, 0 < n ∧ ∀ k, a k = a (k + n)   :=  by sorry
