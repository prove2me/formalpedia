-- Prove2me | Theorems.Thm_lean_workbook_plus_45265
-- name    : lean_workbook_plus_45265
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/566c78cf-c6e0-4ca0-bcd1-e443f96c8366
-- statement:
--   For odd $n$, find $m$ such that $m=(2n^{n-1}-1)n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45265 (n m : ℕ) (h₁ : Odd n) (h₂ : m = (2 * n ^ (n - 1) - 1) * n) : m = (2 * n ^ (n - 1) - 1) * n   :=  by sorry
