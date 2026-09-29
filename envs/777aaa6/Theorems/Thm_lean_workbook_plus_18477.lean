-- Prove2me | Theorems.Thm_lean_workbook_plus_18477
-- name    : lean_workbook_plus_18477
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/de3a3dd5-550b-451a-936d-fa62e0c65930
-- statement:
--   How many finite sequences $x_1,x_2,...x_m$ are there such that each $x_i=1$ or $2$ , and $\sum_{i=1}^mx_i=10?$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18477 (m : ℕ) : { x : Fin m → ℕ | ∀ i, x i = 1 ∨ x i = 2 ∧ ∑ i, x i = 10 } = { x : Fin m → ℕ | ∀ i, x i = 1 ∨ x i = 2 ∧ ∑ i, x i = 10 }   :=  by sorry
