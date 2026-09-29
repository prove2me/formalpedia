-- Prove2me | Theorems.Thm_lean_workbook_plus_57368
-- name    : lean_workbook_plus_57368
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/a67e3232-d720-4528-8e9c-7923c760a643
-- statement:
--   For the following, which values of p determine a convergent series? \n\n(a) $\Sigma_{n=1}^{\infty} \frac{1}{n^p}$ (I do not know how to make the Sigma larger and put the infinity on top and n=1 on bottom....) \n\nI know that this is our basic p-series and that it is convergent when $p > 1$ and divergent when $p \leq 1$ \n\nI think the way to prove this is to see that \n\nIf $p < 0$ , then $\lim_{n \rightarrow \infty} \frac{1}{n^p} = \infty$ \n\nIf $p = 0$ , then $\lim_{n \rightarrow \infty} \frac{1}{n^p} = 1$ \n\nIn both cases, the limit doesn't equal zero so the series' sum cannot converge. \n\nThen we can apply the integral test because $\int_1^\infty \frac{1}{x^p} ,\ dx$ converges if $p > 1$ and diverges if $p \leq 1$ \n\nSo that is that, right? \n\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57368 (p : ℝ) : 1 < p → ∃ l, ∑' n : ℕ, (1/(n^p) : ℝ) = l   :=  by sorry
