-- Prove2me | Theorems.Thm_lean_workbook_plus_26359
-- name    : lean_workbook_plus_26359
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/da523954-7faa-45a3-8c53-ccf95f6c0e4f
-- statement:
--   If $f(n) = \frac{1}{n^2+n}$, what is the value of the sum of $f(1)$, $f(2)$, $f(3)$, $f(4)$, $f(5)$, $f(6)$, $f(7)$, $f(8)$, $f(9)$, and $f(10)$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26359 (f : ℕ → ℚ) (hf : ∀ n, f n = 1/(n^2 + n)) : ∑ i in Finset.range 10, f i = 10/11   :=  by sorry
