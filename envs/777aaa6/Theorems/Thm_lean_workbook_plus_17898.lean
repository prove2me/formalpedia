-- Prove2me | Theorems.Thm_lean_workbook_plus_17898
-- name    : lean_workbook_plus_17898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c699d552-2a6d-40fe-8784-9bcb61419524
-- statement:
--   Let $\alpha,\beta>0$ and a sequence $(a_n)_{n\ge 0}$ for which $\alpha\cdot a_{n+1}+\beta \cdot a_n=0$. Study the nature of this sequence.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17898 (α β : ℝ) (a : ℕ → ℝ) (hα : α > 0) (hβ : β > 0) (ha : ∀ n, α * a (n + 1) + β * a n = 0) : ∃ k : ℝ, ∀ n, a (n + 1) = k * a n   :=  by sorry
