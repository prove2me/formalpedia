-- Prove2me | Theorems.Thm_lean_workbook_plus_33033
-- name    : lean_workbook_plus_33033
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/33a677de-dc9b-4eb5-b4d9-e27131670268
-- statement:
--   Prove that if $ f: \mathbb{R} \to \mathbb{R}$ is a monotonous function satisfying $ f(f(x)) = f( - f(x)) = f(x)^2$, then $ f(x) = f(-x)$ for all $ x\in f(\mathbb{R})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33033 (f : ℝ → ℝ) (h₁ : Monotone f) (h₂ : ∀ x, f (f x) = (f x)^2) (h₃ : ∀ x, f (-f x) = (f x)^2) : ∀ x ∈ Set.range f, f x = f (-x)   :=  by sorry
