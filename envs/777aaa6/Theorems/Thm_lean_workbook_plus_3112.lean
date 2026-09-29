-- Prove2me | Theorems.Thm_lean_workbook_plus_3112
-- name    : lean_workbook_plus_3112
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/16098a94-9872-414d-a105-40d7723ff150
-- statement:
--   Let $f(n)$ be the answer for $\{1,2,3,...n\}$ . Notice that $f(n)$ is the number of permutations which fail to satisfy the condition at precisely the $n$ th place. Thus the number of permutations of $\{1,2,3,...n\}$ which fail at the $k$ th place must be $f(k)\cdot (n-k)!$ , which means that \n$f(n)=n!-f(n-1)\cdot 1!-f(n-2)\cdot 2!-...-f(1)\cdot (n-1)!$ \nso $f(5)=5!-13\cdot 1!-3\cdot 2!-1\cdot 3!-1\cdot 4!=\boxed{71}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3112  (n : ℕ)
  (f : ℕ → ℕ)
  (h₀ : f 1 = 0)
  (h₁ : ∀ n, f (n + 1) = (n + 1)! - ∑ k in Finset.range (n + 1), f k * (n + 1 - k)!):
  f 5 = 71   :=  by sorry
