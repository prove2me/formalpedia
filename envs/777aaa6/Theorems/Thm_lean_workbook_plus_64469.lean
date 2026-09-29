-- Prove2me | Theorems.Thm_lean_workbook_plus_64469
-- name    : lean_workbook_plus_64469
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/091d6cc8-dcbf-454d-9b33-e0d0308f5220
-- statement:
--   Let $x_1>0$ and define $x_{n+1}=\dfrac{n}{x_1+x_2+...+x_n}$ for every $n\in \mathbb{Z_+} $ . Prove that $x_{2004} \le 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64469 (x : ℕ → ℝ) (hx : ∀ n, 0 < x n) (hn : ∀ n, x (n + 1) = n / (∑ i in Finset.range (n + 1), x i)) : x 2004 ≤ 1   :=  by sorry
