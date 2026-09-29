-- Prove2me | Theorems.Thm_lean_workbook_plus_9130
-- name    : lean_workbook_plus_9130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/33aad251-6dd0-4459-a085-937528e3f080
-- statement:
--   Since $f$ is uniformly continuous on $[x,x+1]$ , for any $\epsilon > 0$ we can find a $\delta > 0$ such that $|t_1 - t_2| < \delta \implies |f(t_1) - f(t_2)| < \epsilon$ holds for $t_1,t_2 \in [x,x+1]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9130 {f : ℝ → ℝ} {x : ℝ} :
  UniformContinuousOn f (Set.Icc x (x + 1)) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ t1 t2 : ℝ, t1 ∈ Set.Icc x (x + 1) ∧ t2 ∈ Set.Icc x (x + 1) ∧
      |t1 - t2| < δ → |f t1 - f t2| < ε   :=  by sorry
