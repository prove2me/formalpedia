-- Prove2me | Theorems.Thm_lean_workbook_plus_82573
-- name    : lean_workbook_plus_82573
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3477a8f1-6e6d-4cb8-bb51-728341bd7fe8
-- statement:
--   Let $f(x)=1-a\cos x-b\sin x-A\cos 2x-B\sin 2x,f(x)\ge o ,a,b,A,B \in \mathbb{R}$ .\nProve that $a^2+b^2 \ge 0$ and $A^2+B^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82573 : ∀ a b A B : ℝ, (∀ x : ℝ, 0 ≤ 1 - a * Real.cos x - b * Real.sin x - A * Real.cos (2 * x) - B * Real.sin (2 * x)) → a ^ 2 + b ^ 2 ≥ 0 ∧ A ^ 2 + B ^ 2 ≥ 0   :=  by sorry
