-- Prove2me | Theorems.Thm_lean_workbook_plus_28664
-- name    : lean_workbook_plus_28664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d65dda19-9638-4ef1-b6a4-fe4b39d204e7
-- statement:
--   Using the close form of an infinite geometric series: $\sum_{n=1}^{\infty}ar^{n-1}=\frac{a}{1-r}$ where $a$ is the first term, and $r$ is the common ratio, we obtain $p=\frac{\frac{1}{2}}{1-\frac{1}{4}}=\frac{2}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28664  (a : ℝ)
  (h₀ : a = 1 / 2)
  (r : ℝ)
  (h₁ : r = 1 / 4) :
  a / (1 - r) = 2 / 3   :=  by sorry
