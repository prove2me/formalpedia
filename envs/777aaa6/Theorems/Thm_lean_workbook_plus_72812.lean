-- Prove2me | Theorems.Thm_lean_workbook_plus_72812
-- name    : lean_workbook_plus_72812
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/5613d986-5724-4f7e-9e2a-22a2a472f9a3
-- statement:
--   Equation is $\cos x(1-\sin^2x)=-\sin^2x(1-\sin x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72812 : ∀ x:ℝ, Real.cos x * (1 - Real.sin x ^ 2) = -Real.sin x ^ 2 * (1 - Real.sin x)   :=  by sorry
