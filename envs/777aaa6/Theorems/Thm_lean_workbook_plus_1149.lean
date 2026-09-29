-- Prove2me | Theorems.Thm_lean_workbook_plus_1149
-- name    : lean_workbook_plus_1149
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/841020c0-5e1a-4ee2-b154-274d00d49478
-- statement:
--   Determine the properties of the function $\theta:\mathbb{R}^2\setminus \{(0,0)\}\to \mathbb{R}$ defined by $(x,y) \mapsto \theta(x,y)$, where $\theta$ is the unique real number such that $-\pi<\theta \leq \pi$ and $(x,y)=(r\cos \theta,r\sin \theta)$ with $r=\sqrt{x^2+y^2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1149 (x y : ℝ) (r : ℝ) (hr : r = Real.sqrt (x ^ 2 + y ^ 2)) (hp : -Real.pi < θ ∧ θ ≤ Real.pi) (htr : (x, y) = (r * Real.cos θ, r * Real.sin θ)) : (x, y) = (r * Real.cos θ, r * Real.sin θ) ∧ -Real.pi < θ ∧ θ ≤ Real.pi   :=  by sorry
