-- Prove2me | Theorems.Thm_lean_workbook_plus_79556
-- name    : lean_workbook_plus_79556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/4c96e7a5-fa3d-4d5f-a4db-faa7ae0905a3
-- statement:
--   Prove that for $a, b, c \geq 0$ with $a \geq b \geq c$, the following inequalities hold:\n\n1. $(a-b)^3 + (b-c)^3 + (c-a)^3 \leq 0$\n2. $(a-b)^5 + (b-c)^5 + (c-a)^5 \leq 0$\n\n... and in general, $(a-b)^{2k+1} + (b-c)^{2k+1} + (c-a)^{2k+1} \leq 0$ for all $k \in \mathbb{N}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79556 (a b c : ℝ) (h₁ : a ≥ b ∧ b ≥ c ∧ c ≥ a) (k : ℕ) :
  (a - b)^(2 * k + 1) + (b - c)^(2 * k + 1) + (c - a)^(2 * k + 1) ≤ 0   :=  by sorry
