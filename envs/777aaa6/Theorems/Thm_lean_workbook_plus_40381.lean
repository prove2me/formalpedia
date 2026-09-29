-- Prove2me | Theorems.Thm_lean_workbook_plus_40381
-- name    : lean_workbook_plus_40381
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/aa219f20-a2b8-4cb7-9e13-c29690120b91
-- statement:
--   Let's assign the population at $t=0$ as $p$ . The population at $t=1$ is equal to $p(1+\frac{i}{100})$ . The population at $t=2$ is the population at $t=1$ multiplied by the $1+\frac{j}{100}$ . Plugging in $t=1$ , we get $p(1+\frac{i}{100})(1+\frac{j}{100})=$ . Now we can use our percent increase formula: $t=2$ is our final population value and $t=1$ is our initial population value. Hence, we get $\frac{p(1+\frac{j}{100})(1+\frac{j}{100})-p}{p}$ $*100$ %. Simplifying, we get $\text{(D) } \left(i+j+\frac{ij}{100}\right)\%\quad$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40381  (p i j : ℝ)
  (h₀ : 0 < p)
  (h₁ : 0 < i)
  (h₂ : 0 < j) :
  ((p * (1 + i / 100) * (1 + j / 100) - p) / p) * 100 = i + j + (i * j / 100)   :=  by sorry
