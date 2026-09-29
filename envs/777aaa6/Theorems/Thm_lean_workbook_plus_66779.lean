-- Prove2me | Theorems.Thm_lean_workbook_plus_66779
-- name    : lean_workbook_plus_66779
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/9e3d1830-eb1e-4f21-86df-00aad368cf70
-- statement:
--   If $y \neq 0$, then: $72x^3 + 4xy^2 = 11y^3 \Leftrightarrow 72\left( \frac {x}{y}\right)^3 + 4\frac {x}{y} - 11 = 0$; and if: $\frac {x}{y} = t$, $72t^3 + 4t - 11 = 0$ and $t = \frac {1}{2}$ solution $\Rightarrow x = 2y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66779  (x y : ℝ)
  (h₀ : y ≠ 0)
  (h₁ : 72 * x^3 + 4 * x * y^2 = 11 * y^3) :
  72 * (x / y)^3 + 4 * (x / y) - 11 = 0 ∧ x = 2 * y   :=  by sorry
