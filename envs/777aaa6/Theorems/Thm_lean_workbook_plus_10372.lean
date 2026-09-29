-- Prove2me | Theorems.Thm_lean_workbook_plus_10372
-- name    : lean_workbook_plus_10372
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/536b2d53-66f2-4703-bc0c-69269f5a9e0e
-- statement:
--   Prove that the function $ f: \mathbb{R}\to\mathbb{R}$ which is continuous on $ \mathbb{R}$ and satisfies $ 6f(f(x)) = 2f(x) + x$ for every $ x\in \mathbb{R}$ is injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10372 (f : ℝ → ℝ) (hf : Continuous f) (h : ∀ x, 6 * f (f x) = 2 * f x + x) : Function.Injective f   :=  by sorry
