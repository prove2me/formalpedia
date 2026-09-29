-- Prove2me | Theorems.Thm_lean_workbook_plus_49780
-- name    : lean_workbook_plus_49780
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c9c08cfd-ea13-4b0f-8954-5786c35d46bd
-- statement:
--   If $b \ge 2$ in the recursion $v_{i+1}^{(1)} = b v_i^{(1)} - v_{i-1}^{(1)}$, then $v_1^{(1)} = v_2^{(1)} = \cdots = v_n^{(1)} = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49780 (n : ℕ) (b : ℕ) (v : ℕ → ℕ) (h₁ : b ≥ 2) (h₂ : v 0 = 0) (h₃ : v 1 = 0) (h₄ : ∀ i, v (i + 2) = b * v (i + 1) - v i) : ∀ i, v i = 0   :=  by sorry
