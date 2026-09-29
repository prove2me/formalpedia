-- Prove2me | Theorems.Thm_lean_workbook_plus_44320
-- name    : lean_workbook_plus_44320
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/1c651092-6e49-4094-af31-327419efa35a
-- statement:
--   Find the formula of the general term in the sequence $x_n$ knowing that $x_1=1, x^2_{n}+1=(n+1)x^2_{n+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44320 (x : ℕ → ℝ) (n : ℕ) (hx: x 1 = 1) (hn: ∀ n, (x n)^2 + 1 = (n + 1) * (x (n + 1))^2) : ∃ f : ℕ → ℝ, ∀ n, x n = f n   :=  by sorry
