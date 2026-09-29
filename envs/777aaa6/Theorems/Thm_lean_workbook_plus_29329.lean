-- Prove2me | Theorems.Thm_lean_workbook_plus_29329
-- name    : lean_workbook_plus_29329
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3d68269c-e8f4-4ee5-b96d-b3b86620a483
-- statement:
--   The function: $f(t) = {t^5}$ is convex in $[0, + \infty )$, so: $\forall \mathop {}\limits^{} x,y \in [0, + \infty )$, $f\left( {\frac{{x + y}}{2}} \right) \le \frac{{f(x) + f(y)}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29329  (x y : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y) :
  ((x + y) / 2)^5 ≤ (x^5 + y^5) / 2   :=  by sorry
