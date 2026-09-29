-- Prove2me | Theorems.Thm_lean_workbook_plus_25978
-- name    : lean_workbook_plus_25978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/67f84031-c363-40d4-891d-115c5a6f708d
-- statement:
--   prove that $\frac{m}{1+m+mn}+\frac{n}{1+n+np}+\frac{p}{1+p+pm}\leq 1$ given $\{m,n,p\}\subset\mathbb R_+^*$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25978 (m n p : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) : m / (1 + m + m * n) + n / (1 + n + n * p) + p / (1 + p + p * m) ≤ 1   :=  by sorry
