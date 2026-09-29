-- Prove2me | Theorems.Thm_lean_workbook_plus_70357
-- name    : lean_workbook_plus_70357
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/db0cc206-d101-4e78-bf54-ed436e6e8d3e
-- statement:
--   Prove that $\sum_{r=0}^n \binom{n}{r} z^r = (1+z)^n$ for all $n \in \mathbb{N}$ and $z \in \mathbb{C}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70357 (n : ℕ) (z : ℂ) : ∑ r in Finset.range (n + 1), choose n r * z ^ r = (1 + z) ^ n   :=  by sorry
