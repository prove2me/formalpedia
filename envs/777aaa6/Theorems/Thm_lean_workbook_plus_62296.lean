-- Prove2me | Theorems.Thm_lean_workbook_plus_62296
-- name    : lean_workbook_plus_62296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/51e25776-7132-45c0-a7d7-a85294daa032
-- statement:
--   If $f(n) > m$ for all $n > m$, then $f_i(n) \geq m+1$ for all $n \geq m+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62296 (f : ℕ → ℕ) (m : ℕ) (h₁ : ∀ n, n > m → f n > m) : ∀ n, n ≥ m + 1 → f n ≥ m + 1   :=  by sorry
