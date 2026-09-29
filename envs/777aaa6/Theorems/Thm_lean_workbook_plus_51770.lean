-- Prove2me | Theorems.Thm_lean_workbook_plus_51770
-- name    : lean_workbook_plus_51770
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/37e03083-43f0-4b0c-973b-110c9d104d7d
-- statement:
--   Verify the solution $f(n) = n + a$ where $a \in \mathbb{N}_0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51770 (f : ℕ → ℕ) (a : ℕ) (h₁ : ∀ n, f n = n + a) : ∀ n, f n = n + a   :=  by sorry
