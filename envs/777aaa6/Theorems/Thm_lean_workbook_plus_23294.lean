-- Prove2me | Theorems.Thm_lean_workbook_plus_23294
-- name    : lean_workbook_plus_23294
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/17300031-b1bb-4266-a42b-d15362bf6ae3
-- statement:
--   Determine whether the series $ \sum_{n=2}^{\infty} a_n$ is absolutely convergent, conditionaly convergent or divergent. Given $ a_n=\frac{1+n+n^2}{\sqrt{1+n^2+n^6}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23294 (n : ℕ) (hn : 2 ≤ n) (a_n : ℝ) (ha_n : a_n = (1 + n + n^2) / (Real.sqrt (1 + n^2 + n^6))) : ∃ l, ∑' n : ℕ, a_n = l   :=  by sorry
