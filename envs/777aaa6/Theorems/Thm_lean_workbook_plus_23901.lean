-- Prove2me | Theorems.Thm_lean_workbook_plus_23901
-- name    : lean_workbook_plus_23901
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/81fb4363-1624-4fdf-ae86-e36a67ac29aa
-- statement:
--   Consider $ 2^i$ , $ 0 \le i \le 10$ . It is added $ i$ times and subtracted $ 10 - i$ times, so in total it is added $ 2i - 10$ times. Hence, we want the sum \n\n $ \sum_{i = 0}^{10} (2i - 10)2^i$ \n\nWe could brute-force this, but there's another way (that might not be easier, but requires less calculation): \n\n \begin{align*}\sum_{i = 0}^{10} (2i - 10)2^i&= 2 \left( \sum_{i = 0}^{10} i2^i - 5\sum_{i = 0}^{10}\cdot 2^i \right)\\&=2 \left( \left( \sum_{i = 1}^{10} 2^i + \sum_{i = 2}^{10} 2^i + \ldots + \sum_{i = 10}^{10}2^i \right) - 5(2^{11} - 1) \right)\\&= 2 (2(2^{10} - 1 + 2^{10} - 2 + 2^{10} - 2^2 + \ldots + 2^{10} - 2^9) - 5(2^{11} - 1))\\&= 2(2(10\cdot 2^{10} - (2^{10} - 1)) - 5(2^{11} - 1))\\&= 2(4\cdot 2^{11} + 7)\\&= 2(8199)\\&= 16398\end{align*} \n\nso the answer is $ 398$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23901 :
  ∑ k in (Finset.range 11), ((2 : ℤ)^k * (2 * ↑k - 10)) = 16398   :=  by sorry
