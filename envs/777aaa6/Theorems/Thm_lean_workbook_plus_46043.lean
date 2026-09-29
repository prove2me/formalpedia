-- Prove2me | Theorems.Thm_lean_workbook_plus_46043
-- name    : lean_workbook_plus_46043
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/5d55cafd-7241-4cc3-af8c-48c085eaf3b4
-- statement:
--   Prove that the maximum value of $a\sin\theta+b\cos\theta$ is $\sqrt{a^2+b^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46043 (a b : ℝ) : ∀ θ : ℝ, a * Real.sin θ + b * Real.cos θ ≤ Real.sqrt (a ^ 2 + b ^ 2)   :=  by sorry
