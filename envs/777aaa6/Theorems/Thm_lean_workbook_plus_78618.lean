-- Prove2me | Theorems.Thm_lean_workbook_plus_78618
-- name    : lean_workbook_plus_78618
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/756fe9aa-e0a3-4bbd-9c28-79af6e210058
-- statement:
--   Prove that $ {{n}\choose{r}} = {{n}\choose{n-r}}$, by using different arguments.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78618 (n r : ℕ) (h₁ : r ≤ n) (h₂ : n - r ≤ n) : choose n r = choose n (n - r)   :=  by sorry
