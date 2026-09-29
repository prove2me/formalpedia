-- Prove2me | Theorems.Thm_lean_workbook_plus_13705
-- name    : lean_workbook_plus_13705
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/760616cd-a28e-488e-a8f7-4a56e466f21e
-- statement:
--   Basic method (there surely exists something smarter) : $y=\frac{2x}{2x-1}$ with $x\in[1,\frac 32]$ \nAnd so we are looking at $\max_{x\in[1,\frac 32]}f(x)$ with $f(x)=x^3+\frac{8x^3}{(2x-1)^3}$ \nAnd it is easy to see that $f(x)$ is continuous convex over the given interval and so result is \n $\max(f(1),f(\frac 32))=9$ \nQ.E.D.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13705  (x : ℝ)
  (h₀ : 1 ≤ x ∧ x ≤ 3 / 2) :
  x^3 + (8 * x^3) / (2 * x - 1)^3 ≤ 9   :=  by sorry
