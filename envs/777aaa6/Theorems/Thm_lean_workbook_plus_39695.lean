-- Prove2me | Theorems.Thm_lean_workbook_plus_39695
-- name    : lean_workbook_plus_39695
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/bdb5948b-077f-4d69-9f3f-89c75d58ff41
-- statement:
--   Illustrate the use of Cauchy-Schwarz's extended version for $p, q, x, y > 0$: $\frac{x^2}{p} + \frac{y^2}{q} \geq \frac{(x+y)^2}{p+q}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39695 (p q x y : ℝ) (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hy : 0 < y) : (x ^ 2 / p + y ^ 2 / q) ≥ (x + y) ^ 2 / (p + q)   :=  by sorry
