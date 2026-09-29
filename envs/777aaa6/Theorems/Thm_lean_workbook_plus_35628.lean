-- Prove2me | Theorems.Thm_lean_workbook_plus_35628
-- name    : lean_workbook_plus_35628
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/5838200d-b92a-42ed-b520-e703b4be50c8
-- statement:
--   Part BDrawing a free-body diagram, we can see that the only force providing a centripetal force is the static friction force. Setting the friction force equal to the centripetal force, we get $\mu mg = m \frac{v^2}{r}$ . Solving for $\mu$ , we get $\mu = \frac{v^2}{rg}$ . Substituting the values of $v$ , $r$ , and $g$ , we get $\mu = \fbox{0.0034}$ . Note: I used $g = 9.8$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35628  (v r g : ℝ)
  (h₀ : 0 < v ∧ 0 < r ∧ 0 < g)
  (h₁ : v^2 / r = μ * g) :
  μ = v^2 / (r * g)   :=  by sorry
