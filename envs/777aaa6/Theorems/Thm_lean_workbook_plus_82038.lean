-- Prove2me | Theorems.Thm_lean_workbook_plus_82038
-- name    : lean_workbook_plus_82038
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c120a243-205c-41f5-8b53-ea64b9f0f03e
-- statement:
--   In the collision in bringing the momentum there is impulse on the rock that we do through a contact force. Say the rock was moving at velocity $v_0$ and is of mass $m$. So in order to bring it to rest, we have $J=\int_{t_0}^{t_f} F{dt}=-mv_0$. Of course, we can approximate and say that $F$ is roughly constant over this interval, so $F_{rf}\Delta{t}=-mv_0$ so $F_{rf}=\frac{-mv_0}{\Delta{t}}$. The equal reaction force is equal to $F_{fr}=\frac{mv_0}{\Delta{t}}=$ so $F \propto v_0$ or the speed of the rock. So in the collision itself (not the stationary case) our foot is acting against (and opposing) the momentum of the rock. Right?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82038  (m v0 Δt : ℝ)
  (h₀ : 0 < m ∧ 0 < v0 ∧ 0 < Δt)
  (h₁ : m * v0 = F * Δt) :
  F = m * v0 / Δt   :=  by sorry
