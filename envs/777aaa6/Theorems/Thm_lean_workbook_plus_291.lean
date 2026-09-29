-- Prove2me | Theorems.Thm_lean_workbook_plus_291
-- name    : lean_workbook_plus_291
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a0eab48d-ec16-41c2-9f7f-8331b893bf20
-- statement:
--   Let A be a matrix nXn with $a_{ij}\ge{0}$ for every i,j=1,2,...,n and $\sum_{j=1}^{n}a_{ij}=1$ for every i=1,2,..,n. Show that if a is an eigenvalue of A then $|a|\leq{1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_291 (n : ℕ) (hn : 0 < n) (a : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i j, 0 ≤ a i j) (h : ∀ i, ∑ j, a i j = 1) (a_eig : ∃ v : Fin n → ℝ, ∃ l : ℝ, a.mulVec v = l • v) : ∃ v : Fin n → ℝ, ∃ l : ℝ, a.mulVec v = l • v ∧ l ≤ 1 ∧ -1 ≤ l   :=  by sorry
