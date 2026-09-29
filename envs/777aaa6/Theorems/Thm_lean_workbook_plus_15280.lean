-- Prove2me | Theorems.Thm_lean_workbook_plus_15280
-- name    : lean_workbook_plus_15280
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/38eac896-905e-4b37-80f7-fde76974bc77
-- statement:
--   Given a number with $n+1$ many 2007's, it's easy to verify that we can write this as $2007\times10^{4n}+2007\times10^{4n-4}+\ldots+2007\times10^4+2007$. Now we need to show that the above number is divisible by 101 for infinitely many $n$. First note that $10^4-1=(10^2+1)(10^2-1)=101\times99$. So $10^4-1$ is divisible by 101, or equivalently, $10^4\equiv1\mod101$. Furthermore, $10^{4k}\equiv(10^4)^k\equiv1^k\equiv1\mod101$ for any nonnegative integer $k$. Consequently, $2007\times10^{4n}+\ldots+2007\equiv2007+\ldots+2007\equiv2007(n+1)\mod101$. So the number with $n+1$ many 2007's will be divisible by 101 if $n+1$ is divisible by 101. Since our set obviously has infinitely many of those numbers, 101 divides infinitely many of the numbers in the set.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15280 :
  ∀ n : ℕ, 101 ∣ (∑ k in Finset.range (n + 1), 2007 * 10 ^ (4 * k))   :=  by sorry
