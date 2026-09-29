-- Prove2me | Theorems.Thm_lean_workbook_plus_42311
-- name    : lean_workbook_plus_42311
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/af31cf80-5014-47c3-bcd2-08b6e8f51721
-- statement:
--   Proof: Consider the fractions $\dfrac{1}{n}, \dfrac{2}{n}, \ldots, \dfrac{n}{n}$ , and reduce them. There are exactly $\phi(d)$ of them with denominator $d$ , where $d|n$ . So the number of fractions is $\sum_{d|n}\phi(d)$ . But it is also $n$ , so $\sum_{d|n}\phi(d) = n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42311 (n : ℕ) : ∑ k in divisors n, φ k = n   :=  by sorry
