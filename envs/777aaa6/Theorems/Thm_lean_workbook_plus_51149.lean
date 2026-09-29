-- Prove2me | Theorems.Thm_lean_workbook_plus_51149
-- name    : lean_workbook_plus_51149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/453a8d6a-c61c-486b-bd12-fc4f852e6dba
-- statement:
--   Let $k^2\leq n < (k+1)^2$ , so $n=k^2+r$ for some $0\leq r < 2k+1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51149 (n : ℕ) (k : ℕ) (h₁ : k^2 ≤ n) (h₂ : n < (k + 1)^2) : ∃ r : ℕ, n = k^2 + r ∧ r < 2 * k + 1   :=  by sorry
