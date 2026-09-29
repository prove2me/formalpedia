-- Prove2me | Theorems.Thm_lean_workbook_plus_66012
-- name    : lean_workbook_plus_66012
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/bce1d0c3-8674-433d-ae2c-064e763ba053
-- statement:
--   Let $a \cdot m = n$, where $a$ is a positive integer. Then, we see that $Q(x) = x^{am} - 1$. Now let $x^m = y$; then our functions become $P(x) = y^a - 1$ and $Q(x) = y - 1$. Now by the Linear Factor Theorem, when $y = 1$, $P(x) = 0$, so $P(x)$ is divisible by $Q(x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66012  (a m : ℕ)
  (h₀ : 0 < a ∧ 0 < m) :
  (x^m - 1 ∣ x^(a * m) - 1)   :=  by sorry
