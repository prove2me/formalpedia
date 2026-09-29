-- Prove2me | Theorems.Thm_lean_workbook_plus_42974
-- name    : lean_workbook_plus_42974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/09f8faa4-3aca-4f1d-95b9-8d77d0c8cc48
-- statement:
--   Let $a$, $b$, and $c$ be real numbers such that $ab + bc + ca = 3$ and $a + b + c = 5$. Prove that $-1 \leq c \leq \frac{13}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42974 (a b c : ℝ) (h₁ : a + b + c = 5) (h₂ : a * b + b * c + c * a = 3) : -1 ≤ c ∧ c ≤ 13 / 3   :=  by sorry
