-- Prove2me | Theorems.Thm_lean_workbook_plus_40051
-- name    : lean_workbook_plus_40051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8cd8270b-0059-4ed8-bc22-9b6fa53e8200
-- statement:
--   Find the closed form of the sequence defined by $U_1=U_2=1$ and $U_{2k+1}=3U_{2k}+6U_{2k-1}, U_{2k+2}=3U_{2k+1}-6U_{2k}$ for $k \ge 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40051 (U : ℕ → ℤ) (h₁ : U 1 = 1) (h₂ : U 2 = 1) (h₃ : ∀ k, U (2 * k + 1) = 3 * U (2 * k) + 6 * U (2 * k - 1)) (h₄ : ∀ k, U (2 * k + 2) = 3 * U (2 * k + 1) - 6 * U (2 * k)) : ∃ f : ℕ → ℤ, ∀ n, U n = f n   :=  by sorry
