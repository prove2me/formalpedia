-- Prove2me | Theorems.Thm_lean_workbook_plus_46092
-- name    : lean_workbook_plus_46092
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/6db49608-460f-4e38-b883-6e7693430263
-- statement:
--   Find all functions $f,g\colon \mathbb{R}\to\mathbb{R}$ such that $f(x+1)-g(x-1)=c{\cdot }f(x)$ and $g(x+1){\cdot }f(x-1)=c{\cdot }g(x)$ , where $c>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46092 (c : ℝ) (hc : c > 0) : (∀ f g : ℝ → ℝ, (∀ x, f (x + 1) - g (x - 1) = c * f x) ∧ (∀ x, g (x + 1) * f (x - 1) = c * g x) ↔ ∃ a b :ℝ, ∀ x, f x = a ^ x ∧ ∀ x, g x = b ^ x)   :=  by sorry
