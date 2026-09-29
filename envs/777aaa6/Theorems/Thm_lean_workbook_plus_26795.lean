-- Prove2me | Theorems.Thm_lean_workbook_plus_26795
-- name    : lean_workbook_plus_26795
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8c0f65fe-7728-4631-adbd-446743dbb3bd
-- statement:
--   I know my English is poor and, if i made mistakes, please correct me!\n\ni'm not quite sure on part B with what you're saying...but i think i get part A\n\nthe forces on each object are the same, mg down, normal force up which is just mg in the opposite direction, and the frictional force opposite each of their motions which is the normal times $\mu$ .\n\n $F = -\mu mg$ \n $a = -\mu g$ \n\nusing our kinematics equation $v^2 = v_0^2 + 2ax$ \n\n $0 = 4v_0^2 - 2\mu gx_A$ \n $0 = v_0^2 - 2\mu gx_B$ \n $2\mu gx_A = 4v_0^2$ \n $2\mu gx_B = v_0^2$ \n $x_A = (2v_0^2)/(\mu g)$ \n $x_B = (v_0^2)/(2\mu g)$ \n $x = x_A + x_B = (2v_0^2)/(\mu g) + (v_0^2)/(2\mu g) = (5v_0^2)/(2\mu g)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26795 (v₀ : ℝ) (μ : ℝ) (g : ℝ) : (5 * v₀ ^ 2) / (2 * μ * g) = (2 * v₀ ^ 2) / (μ * g) + (v₀ ^ 2) / (2 * μ * g)   :=  by sorry
