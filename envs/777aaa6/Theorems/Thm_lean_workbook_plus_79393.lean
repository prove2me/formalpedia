-- Prove2me | Theorems.Thm_lean_workbook_plus_79393
-- name    : lean_workbook_plus_79393
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/42995fdb-6533-4b70-9f8f-41b171f43bc5
-- statement:
--   Let $m=p+s$ , $n=ps$ , $t = \frac{p^{2}}{(1-s)^{2}}+\frac{s^{2}}{(1-p)^{2}}$ , then $m\leq1$ , and $t=\frac{m^{2}-2n-2m^{3}+6mn+m^{4}-4m^{2}n+2n^{2}}{(1-m+n)^{2}}$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79393  ∀ m n : ℝ, ∀ p s t : ℝ, m = p + s ∧ n = p * s ∧ t = p^2 / (1 - s)^2 + s^2 / (1 - p)^2 →  m ≤ 1 ∧ t = (m^2 - 2 * n - 2 * m^3 + 6 * m * n + m^4 - 4 * m^2 * n + 2 * n^2) / (1 - m + n)^2   :=  by sorry
