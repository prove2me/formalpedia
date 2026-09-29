-- Prove2me | Theorems.Thm_lean_workbook_plus_44335
-- name    : lean_workbook_plus_44335
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/dcbe93a8-4b4c-4ddf-bd10-78965860f088
-- statement:
--   If $a=0$ then done else $\frac{y_{n}}{a^{n}}=\frac{x_{n}}{a^{n}}-\frac{x_{n-1}}{a^{n-1}}(n=1,2,...)$ Therefore $\sum_{k=1}^{n}\frac{y_{k}}{a^{k}}=\frac{x_{n}}{a^{n}}-x_{0}(n=1,2,...)$ also $x_{n}=\sum_{k=0}^{n}a^{n-k}y_{k}(n=0,1,2,...)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44335  (a : ℝ)
  (n : ℕ)
  (x y : ℕ → ℝ)
  (h₀ : a ≠ 0)
  (h₁ : ∀ n, y n = x n - x (n - 1) * a)
  (h₂ : ∑ k in Finset.Icc 1 n, (y k / a^k) = x n / a^n - x 0)
  (h₃ : ∀ n, x n = ∑ k in Finset.range (n + 1), a^(n - k) * y k) :
  x n = ∑ k in Finset.range (n + 1), a^(n - k) * y k   :=  by sorry
