-- Prove2me | Theorems.Thm_lean_workbook_plus_48801
-- name    : lean_workbook_plus_48801
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/a7cd6071-5643-4298-b93f-3830ba876240
-- statement:
--   Letting $n$ be the original number of bacteria and $h$ be the number of hours it takes for the initial number of bacteria to decrease by $50\%$, we have $n \cdot (0.9)^h = \frac{1}{2}n$, so $(0.9)^h = \frac{1}{2}$. Taking the logarithm, we have $h = \log_{0.9}{0.5}$. By the Change of Base Formula, this is $\frac{\log{0.5}}{\log{0.9}}$. Plugging this into a calculator we get $\boxed{6.6}$ hours.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48801  (n : ℝ)
  (h : ℝ)
  (h₀ : 0 < n)
  (h₁ : 0 < h)
  (h₂ : (0.9^h) * n = 0.5 * n) :
  h = Real.log 0.5 / Real.log 0.9   :=  by sorry
