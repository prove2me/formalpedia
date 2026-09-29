-- Prove2me | Theorems.Thm_lean_workbook_plus_17979
-- name    : lean_workbook_plus_17979
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7050b29a-b62f-45e2-b350-bcee7e59ac8d
-- statement:
--   For all positive integer $n$ , show that\n $$\dfrac{n}{n+1}-\dfrac{n(n-1)}{(n+1)(n+2)}+\dfrac{n(n-1)(n-2)}{(n+1)(n+2)(n+3)}-\cdots + (-1)^{n-1}\cdot \dfrac{n(n-1)\cdots 2\cdot 1}{(n+1)(n+2)\cdots (n+n)} = \dfrac{1}{2}$$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17979 : ∀ n : ℕ, (∑ k in Finset.range n, (-1 : ℤ)^k * (∏ l in Finset.range k, (n - l)) / (∏ l in Finset.range k, (n + l))) = 1 / 2   :=  by sorry
