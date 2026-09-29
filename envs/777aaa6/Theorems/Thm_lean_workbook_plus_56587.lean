-- Prove2me | Theorems.Thm_lean_workbook_plus_56587
-- name    : lean_workbook_plus_56587
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d4b5fd40-b046-4afb-a54d-1ea96ff7033d
-- statement:
--   At an elementary level (without explicitly invoking the Stirling approximation):\n\n$\ln[(2k-1)!(2k)!]=\ln 1+2\ln 2+2\ln 3+\cdots+2\ln(2k-1)+\ln(2k)$ That sum on the right is a trapezoid rule approximation to $\int_1^{2k}2\ln x\,dx$ . Since the logarithm is concave, the trapezoid rule estimate is (slightly) less than the integral, and\n\n\begin{align*}\ln[(2k-1)!(2k)!] &< \int_1^{2k}2\ln x\,dx = 4k\ln(2k)-4k+2\\ \sqrt{\ln[(2k-1)!(2k)!]} &< \sqrt{4k\ln(2k)-4k+2}\end{align*}Now, we want to sum that. Trying to compare that to an integral isn't a good idea - square roots of logarithms are not something we want to work with. Instead, we look at the target; we want to prove the square root of the sum is less than $n$ , or equivalently that the sum is less than $n^2$ . That will be true if the $k$ th term of the sum is less than $2k-1$ , as $\sum_{k=1}^n [2k-1]=n^2$ .\n\n\begin{align*}\sqrt{4k\ln(2k)-4k+2} &\stackrel{?}{\le} 2k-1\\ 4k\ln(2k)-4k+2&\stackrel{?}{\le} 4k^2-4k+1\\ 4k\ln(2k)&\stackrel{?}{\le} 4k^2-1\end{align*}We have that $\ln 2\approx 0.693 < 1-\frac14$ . Then for positive integer $k$ , $\ln(2k)\le \ln(2^k)\le k\ln 2 < k-\frac{k}{4}\le k-\frac14$ . Using this,\n\n\begin{align*} 4k\ln(2k) &< 4k(k-\frac14) = 4k^2-k\le 4k^2-1 \\ \sqrt{4k\ln(2k)-4k+2} &< 2k-1\\ \sum_{k=1}^n \sqrt{4k\ln(2k)-4k+2} &< \sum_{k=1}^n 2k-1 = n^2\\ \sqrt{\sum_{k=1}^n\sqrt{\ln [(2k-1)!(2k)!]}}\ &< n\end{align*}Done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56587 :
  ∀ n : ℕ,
    Real.sqrt (∑ k in Finset.Icc 1 n, Real.sqrt (Real.log ((2 * k - 1)! * (2 * k)!))) < n   :=  by sorry
