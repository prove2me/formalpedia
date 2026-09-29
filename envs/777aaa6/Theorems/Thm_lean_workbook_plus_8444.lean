-- Prove2me | Theorems.Thm_lean_workbook_plus_8444
-- name    : lean_workbook_plus_8444
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3380de24-4a41-4814-a946-482adc33181e
-- statement:
--   We also have: $\sum_{i=1}^n \sqrt{a_i}\left(\frac{1}{\sqrt{a_i}}-\frac{1}{\sqrt{a_{i+1}}}\right)^2\geq 0$ \n\n $\Rightarrow \sum_{i=1}^n\left(\frac{1}{\sqrt{a_i}} - \frac{2}{\sqrt{a_{i+1}}} + \frac{\sqrt{a_i}}{a_{i+1}}\right)\geq 0$ \n\n $\Rightarrow \sum_{i=1}^n\left(\frac{\sqrt{a_i}}{a_{i+1}} - \frac{1}{\sqrt{a_i}}\right)\geq -\frac{1}{\sqrt{a_1}}+ \frac{2}{\sqrt{a_{n+1}}}$ \n\n $\Rightarrow S_n\leq \frac{1}{\sqrt{a_1}} - \frac{2}{\sqrt{a_{n+1}}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8444  (a : ℕ → NNReal)
  (n : ℕ) :
  0 ≤ ∑ i in Finset.range n, (Real.sqrt (a i)) * (1 / Real.sqrt (a i) - 1 / Real.sqrt (a (i + 1)))^2   :=  by sorry
