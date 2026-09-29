-- Prove2me | Theorems.Thm_lean_workbook_plus_15332
-- name    : lean_workbook_plus_15332
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/db957dc5-fe3d-402e-ac2f-299a7b11c6c7
-- statement:
--   A generalisation: If the integers satisfy $gcd(m,n)=1$ ,then $\exists N_{0}$ ,an integer, such that $\forall n \ge N_0$ $\exists$ integers $a$ and $b$ such that $n=ma+nb$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15332 (m n : ℤ) (h : m.gcd n = 1) : ∃ N : ℕ, ∀ n : ℤ, n >= N → ∃ a b : ℤ, n = m * a + n * b   :=  by sorry
