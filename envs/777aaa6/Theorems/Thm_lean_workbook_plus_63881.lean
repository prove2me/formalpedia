-- Prove2me | Theorems.Thm_lean_workbook_plus_63881
-- name    : lean_workbook_plus_63881
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/a120ccbc-c237-4873-b6c0-b96103049847
-- statement:
--   Now, using Cauchy-Schwarz inequality, we also have, $20\sum_{v=1}^{20}d_v^2\geqslant \left(\sum_{v=1}^{20}d_v\right)^2 = 40000$, implying $\sum_{v=1}^{20}d_v^2\geqslant 2000$. Thus, we have an equality in Cauchy-Schwarz, which holds if and only if $d_1=\cdots=d_{20}=10$, that is, if and only if the graph is regular.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63881  (d : ℕ → ℕ)
  (h₀ : ∑ v in Finset.Icc 1 20, d v = 400)
  (h₁ : ∑ v in Finset.Icc 1 20, (d v)^2 = 20 * (∑ v in Finset.Icc 1 20, d v)^2 / 400) :
  ∑ v in Finset.Icc 1 20, (d v)^2 ≥ 2000   :=  by sorry
