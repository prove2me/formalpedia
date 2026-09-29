-- Prove2me | Theorems.Thm_lean_workbook_plus_56868
-- name    : lean_workbook_plus_56868
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/739fbd94-3d4f-45e2-8932-1c256f45aea2
-- statement:
--   Let $p_A(n), p_B(n)$ denote the length n strings ending in $A$ and $B$ . Then we have $p(n) = p_A(n) + p_B(n)$ , $p(n+1) = p(n) + p(n-1) + p_B(n-2)$ and $p_A(n) = p_B(n-1) + p_B(n-2) + p_B(n-3)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56868 (p_A p_B p : ℕ → ℕ) (h₀ : ∀ n, p n = p_A n + p_B n) (h₁ : ∀ n, p (n + 1) = p n + p (n - 1) + p_B (n - 2)) (h₂ : ∀ n, p_A n = p_B (n - 1) + p_B (n - 2) + p_B (n - 3)) : ∀ n, p n = p_A n + p_B n   :=  by sorry
