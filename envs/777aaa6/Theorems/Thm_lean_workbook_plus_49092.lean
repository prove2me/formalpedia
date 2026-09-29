-- Prove2me | Theorems.Thm_lean_workbook_plus_49092
-- name    : lean_workbook_plus_49092
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/34585aa2-cfee-4746-bdf8-88b3149b8dcf
-- statement:
--   Find a continuous function $f: \mathbb{R} \rightarrow \mathbb{R}$ such that for all $a \in A$ and for all $b \in \mathbb{R}$, the following functional equation holds: $f(a + b) + f(a - b) = 2f(a)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49092 (A : Set ℝ) : ∃ f : ℝ → ℝ, Continuous f ∧ ∀ a ∈ A, ∀ b, f (a + b) + f (a - b) = 2 * f a   :=  by sorry
