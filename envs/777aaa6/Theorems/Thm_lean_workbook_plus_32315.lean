-- Prove2me | Theorems.Thm_lean_workbook_plus_32315
-- name    : lean_workbook_plus_32315
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/8d951e96-ec21-4585-b86b-3c30a4b97e52
-- statement:
--   If $n$ is a positive integer odd number, prove that $1\cdot 2^2\cdot 3^3......\cdot n^n >\sqrt{(\dfrac{n+1}{2})^{n(n+1)}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32315 : ∀ n : ℕ, n > 0 ∧ n % 2 = 1 → (∏ i in Finset.range n, i^i) > ((n + 1) / 2)^(n * (n + 1))   :=  by sorry
