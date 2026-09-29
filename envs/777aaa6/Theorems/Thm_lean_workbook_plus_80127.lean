-- Prove2me | Theorems.Thm_lean_workbook_plus_80127
-- name    : lean_workbook_plus_80127
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d86a9046-781d-4030-9e18-a30d86bc6d17
-- statement:
--   Suppose we have $f(x)\le a_n(x+1)$ $\forall x\ge 1$ for some $a_n\ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80127 (f : ℝ → ℝ) (a : ℕ → ℝ) (n : ℕ) (h₀ : a n ≥ 1) (h₁ : ∀ x ≥ 1, f x ≤ a n * (x + 1)) : ∀ x ≥ 1, f x ≤ a n * (x + 1)   :=  by sorry
