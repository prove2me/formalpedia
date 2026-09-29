-- Prove2me | Theorems.Thm_lean_workbook_plus_60566
-- name    : lean_workbook_plus_60566
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e716912b-b631-43ee-b8fd-c50816a10865
-- statement:
--   So there is a $n_0\in\mathbb{N}$ such that for all $n\ge n_0$ then $a_n$ is constant
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60566 (a : ℕ → ℕ) (n₀ : ℕ) (h : ∀ n ≥ n₀, a n = a n₀) : ∃ n₀, ∀ n ≥ n₀, a n = a n₀   :=  by sorry
