-- Prove2me | Theorems.Thm_lean_workbook_plus_26898
-- name    : lean_workbook_plus_26898
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2e83835a-aa11-4946-8aba-ab3fbeb40a1f
-- statement:
--   Given a positive integer $n$ and a real number $k$, consider the following equation in $x$: $(x-1)(x-2)(x-3)...(x-n)=k$. Which of the following statements about this equation is true?\n(a) If $n=3$, then the equation has no real solution $x$ for some values of $k$.\n(b) If $n$ is even, then the equation has a real solution $x$ for any given value of $k$.\n(c) If $k \geq 0$ then the equation has (at least) one real solution $x$.\n(d) The equation never has a repeated solution $x$ for any given values of $k$ and $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26898 (n : ℕ) (k : ℝ) : (∏ i in Finset.range n, (x - i)) = k → ∃ x, (∏ i in Finset.range n, (x - i)) = k   :=  by sorry
