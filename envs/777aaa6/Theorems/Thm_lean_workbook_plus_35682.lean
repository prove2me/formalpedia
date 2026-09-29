-- Prove2me | Theorems.Thm_lean_workbook_plus_35682
-- name    : lean_workbook_plus_35682
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/43b45dde-875d-44b8-8d8d-0acab4614600
-- statement:
--   Let $ p$ be prime number and $ a_0,\ a_1,\ \cdots,\ a_{n-1}\ (n\geq 2)$ be integers. Consider a polynomial with degree $ n$ : $ f(x)=x^n+pa_{n-1}x^{n-1}+\cdots +pa_i x^{i}+\cdots +pa_0.$ (1) If the equation $ f(x)=0$ has integral solution $ \alpha$ , then prove that $ \alpha$ is divisible by $ p$ . (2) If $ a_0$ isn't divisible by $ p$ , then prove that the equation $ f(x)=0$ doesn't have integral solution.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35682 (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℤ) (f : ℤ → ℤ) (hf: f x = x ^ n + (∑ i in Finset.range n, p * a i * x ^ i)) : (∃ x, f x = 0) → ∃ x, p ∣ x   :=  by sorry
