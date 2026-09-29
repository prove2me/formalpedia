-- Prove2me | Theorems.Thm_lean_workbook_plus_48848
-- name    : lean_workbook_plus_48848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ba180bc3-a570-4ebe-88fd-4a53e49e43cc
-- statement:
--   Let $a$ and $b$ be real numbers with $0\le a, b\le 1$ . Prove that $$\frac{a}{b + 1}+\frac{kb}{a + 1}\le k$$ Where $k\geq 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48848 (a b : ℝ) (hab : 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1) (k : ℝ) (hk : k ≥ 1) : a / (b + 1) + k * b / (a + 1) ≤ k   :=  by sorry
