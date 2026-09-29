-- Prove2me | Theorems.Thm_lean_workbook_plus_9926
-- name    : lean_workbook_plus_9926
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c09dfd97-d7b2-4c2f-9269-838d465e2862
-- statement:
--   Suppose $f(x)$ is a rational function such that $3f\left(\dfrac{1}{x}\right)+\dfrac{2f(x)}{x}=x^2$ for $x\neq 0$ . Find $f(-2)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9926 (f : ℝ → ℝ) (hf : ∀ x ≠ 0, 3 * f (1 / x) + (2 * f x) / x = x^2) : f (-2) = 67 / 20   :=  by sorry
