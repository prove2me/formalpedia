-- Prove2me | Theorems.Thm_lean_workbook_plus_38237
-- name    : lean_workbook_plus_38237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2c23d145-c8c8-4c95-84bc-0b69f48fb6f7
-- statement:
--   $p_n$ is the nearest integer to $q_n\sqrt{2}$, for $n$ large $|q_n\sqrt{2}-p_n|<1/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38237 (p q : ℕ → ℕ) (n : ℕ) (h₁ : ∀ n, p n = Int.floor (q n * Real.sqrt 2)) (h₂ : ∀ n, q n * Real.sqrt 2 - p n < 1 / 2) : ∃ n, q n * Real.sqrt 2 - p n < 1 / 2 ∧ p n = Int.floor (q n * Real.sqrt 2)   :=  by sorry
