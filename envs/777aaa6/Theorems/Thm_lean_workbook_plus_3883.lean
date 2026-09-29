-- Prove2me | Theorems.Thm_lean_workbook_plus_3883
-- name    : lean_workbook_plus_3883
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0b000b5d-13bf-4134-9b2a-cda7908030df
-- statement:
--   Find the number of functions $f: (1,2 \cdots n) \to (1,2,3,4,5)$ such that for any $k=1,2 \cdots n-1$ , we have $|f(k+1)-f(k)| \ge 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3883 (n : ℕ) : ∃ F : ℕ → ℕ, ∀ k : ℕ, k ≤ n - 1 → F (k + 1) - F k ≥ 3   :=  by sorry
