-- Prove2me | Theorems.Thm_lean_workbook_plus_13963
-- name    : lean_workbook_plus_13963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d944c24c-11c6-42e7-9f6b-4039897c791a
-- statement:
--   Let $f(m,n)$ be the expected number of points Alice gets with $m$ red and $n$ black cards. Remark that $f(m,0) = f(0, m) = m$ , and also $f(m,m) = \tfrac{1}{2} + f(m,m-1)$ for all $m$ . Now, for $m\ne n$ , we have $ f(m,n) = \tfrac{n}{m + n}\left(f(m,n-1) + T(n > m)\right) + \tfrac{m}{m + n}\left(f(m-1,n) + T(m > n)\right),$ where we define $T(S) = 1$ if $S$ is true and $T(S) = 0$ if $S$ is false for an assertion $S$ . Use this recursion a few times to get $f(3,3) = \tfrac{41}{10}\to\boxed{051}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13963  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ m, f m 0 = m)
  (h₁ : ∀ m, f 0 m = m)
  (h₂ : ∀ m, f m m = 1 / 2 + f m (m - 1))
  (h₃ : ∀ m n, m ≠ n → f m n = n / (m + n) * (f m (n - 1) + if n > m then 1 else 0) + m / (m + n) * (f (m - 1) n + if m > n then 1 else 0)) :
  f 3 3 = 41 / 10   :=  by sorry
