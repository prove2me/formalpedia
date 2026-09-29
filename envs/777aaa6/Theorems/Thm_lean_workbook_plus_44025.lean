-- Prove2me | Theorems.Thm_lean_workbook_plus_44025
-- name    : lean_workbook_plus_44025
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6e85fc1d-ba80-4505-972a-032a106fd0b6
-- statement:
--   And the sequence $v_n=\frac{(3+2\sqrt 2)^{n+1}-(3-2\sqrt 2)^{n+1}}{2\sqrt 2}$ is such that $v_0=2$ and $v_1=12$ and $v_{n+2}=6v_{n+1}-v_n$ and so is made of integer elements.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44025 (v : ℕ → ℤ) (h₀ : v 0 = 2) (h₁ : v 1 = 12) (h₂ : ∀ n, v (n + 2) = 6 * v (n + 1) - v n) : ∀ n, ∃ k : ℤ, v n = k   :=  by sorry
