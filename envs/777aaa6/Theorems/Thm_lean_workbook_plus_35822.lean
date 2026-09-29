-- Prove2me | Theorems.Thm_lean_workbook_plus_35822
-- name    : lean_workbook_plus_35822
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/052252df-6a6b-4abf-a2a0-65bb511f4aee
-- statement:
--   Prove that the function $f(x) = x^3$ is one-to-one.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35822 (f : ℝ → ℝ) (h₁ : ∀ x, f x = x^3) : Function.Injective f   :=  by sorry
