-- Prove2me | Theorems.Thm_lean_workbook_plus_41721
-- name    : lean_workbook_plus_41721
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ea962bb0-d82d-48e3-ac91-b6143be3348c
-- statement:
--   We can also do this with simple manipulations of binomial coefficients: $ \binom{n}{k} = \binom{n - 1}{k - 1} + \binom{n - 2}{n - 1} + \ldots + \binom{k - 1}{k - 1}$ and $ \frac{1}{j} \binom{m - 1}{j - 1} = \frac{1}{m} \binom{m}{j}$ , so $ \frac{1}{k} \binom{n}{k} = \frac{1}{n} \binom{n}{k} + \frac{1}{n - 1}\binom{n - 1}{k} + \ldots + \frac{1}{k}\binom{k}{k}$ . This turns our sum into a double sum $ \sum_{k = 1}^n \frac{1}{k} + \sum_{k = 1}^n \sum_{j = k}^n \frac{1}{j} \binom{j}{k}$ , and reversing the order gives $ \sum_{k = 1}^n \frac{1}{k} + \sum_{j = 1}^n \sum_{k = 1}^j \frac{1}{j} \binom{j}{k} = \sum_{j = 1}^n \sum_{k = 0}^j \frac{1}{j} \binom{j}{k} = \sum_{j = 1}^n \frac{2^j}{j}$ , as desired.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41721 : ∀ n : ℕ, ∑ k in Finset.Icc 1 n, (1 : ℚ)/k * (n.choose k) = ∑ j in Finset.Icc 1 n, (2^j)/j   :=  by sorry
