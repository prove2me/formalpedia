-- Prove2me | Theorems.Thm_lean_workbook_plus_6074
-- name    : lean_workbook_plus_6074
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/09e2873f-f941-4092-91a8-454617aa6c0f
-- statement:
--   For all $1 \leq i \leq j \leq k \leq 100$ we have $a_k^2 \leq a_i^2 + a_j^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6074 (a : ℕ → ℝ) (h : ∀ i j k : ℕ, 1 ≤ i ∧ i ≤ j ∧ j ≤ k ∧ k ≤ 100 → a k ^ 2 ≤ a i ^ 2 + a j ^ 2) : ∀ i j k : ℕ, 1 ≤ i ∧ i ≤ j ∧ j ≤ k ∧ k ≤ 100 → a k ^ 2 ≤ a i ^ 2 + a j ^ 2   :=  by sorry
