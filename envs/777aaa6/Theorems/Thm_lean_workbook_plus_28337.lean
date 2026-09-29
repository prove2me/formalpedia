-- Prove2me | Theorems.Thm_lean_workbook_plus_28337
-- name    : lean_workbook_plus_28337
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8fca14d0-1a4d-4f53-820a-a72fbebf970d
-- statement:
--   Note that $a_n=\frac{(2+\sqrt{3})^{2n+1}+(2-\sqrt{3})^{2n+1}}{4}$ . Define $b_n:=\frac{1}{\sqrt{2}}\left(\left(\frac{\sqrt{3}+1}{\sqrt{2}}\right)^{2n+1}-\left(\frac{\sqrt{3}-1}{\sqrt{2}}\right)^{2n+1}\right)$ . We see that $\left\{b_n\right\}$ satisfies $b_0=1$ , $b_1=5$ , and $b_n=4b_{n-1}-b_{n-2}$ for all $n \geq 2$ . Note that $b_n$ is odd for each $n$ . Now, we may write $a_n=\left(\frac{b_n+1}{2}\right)^2+\left(\frac{b_n-1}{2}\right)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28337  (a : ℕ → ℕ)
  (b : ℕ → ℕ)
  (h₀ : b 0 = 1)
  (h₁ : b 1 = 5)
  (h₂ : ∀ n ≥ 2, b n = 4 * b (n - 1) - b (n - 2))
  (h₃ : ∀ n, Odd (b n))
  (h₄ : ∀ n, a n = (b n + 1)^2 / 2^2 + (b n - 1)^2 / 2^2) :
  ∀ n, ∃ x y : ℕ, a n = x^2 + y^2   :=  by sorry
