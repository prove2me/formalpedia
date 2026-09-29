-- Prove2me | Theorems.Thm_lean_workbook_plus_25310
-- name    : lean_workbook_plus_25310
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3f082ceb-251c-4f27-8384-d90472c007ae
-- statement:
--   Find $ \lim_{n \to \infty} \left\{(a + b\sqrt {c})^n\right\}$ given $ a = 1 + [b\sqrt c]$ and $ \sqrt c \not\in \mathbb{Q}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25310 (a b c : ℝ) (h₁ : a = 1 + b * Real.sqrt c) (h₂ : Real.sqrt c ∉ Set.range ((↑) : ℚ → ℝ)) : ∃ n : ℕ, ∀ ε : ℝ, ε > 0 → |(a + b * Real.sqrt c)^n - 1| < ε   :=  by sorry
