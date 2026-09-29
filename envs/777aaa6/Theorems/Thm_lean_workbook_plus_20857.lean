-- Prove2me | Theorems.Thm_lean_workbook_plus_20857
-- name    : lean_workbook_plus_20857
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f240c2f6-8e8f-42ea-889a-15e5a29c2d31
-- statement:
--   For each integer $n\geq 0$ , let $p_n$ denote the probability that the $n^{\text{th}}$ flip after the first one is heads, with $p_0 = 1$ . Then by the Total Probability Formula, \n\begin{align*}p_{n+1} &= \operatorname{Pr}\{(n+1)^{\text{st}}\text{ heads}\mid n^{\text{th}}\text{ heads}\}\Pr\{n^{\text{th}}\text{ heads}\} \&\hspace{10ex}+ \operatorname{Pr}\{(n+1)^{\text{st}}\text{ heads}\mid n^{\text{th}}\text{ tails}\}\Pr\{n^{\text{th}}\text{ tails}\}\&= \frac23p_n + \frac13(1-p_n) = \frac13 + \frac13p_n.\end{align*} It is straightforward to derive $p_n = \tfrac{1+3^n}{2\cdot 3^n}$ , and now the desired answer is obtained by plugging in $n=2010$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20857  (p : ℕ → ℚ)
  (h₀ : p 0 = 1)
  (h₁ : ∀ n, p (n + 1) = 2 / 3 * p n + 1 / 3 * (1 - p n)) :
  p 2010 = (1 + 3^2010) / (2 * 3^2010)   :=  by sorry
